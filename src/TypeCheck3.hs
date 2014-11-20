{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
module TypeCheck3
  ( -- * Global state
    TCState'
  , emptyTCState'
    -- * Program checking
  , checkProgram
    -- * Interactive mode
  , Command
  , parseCommand
  , runCommand
  ) where

import           Control.Lens                     ((^.))
import qualified Control.Lens                     as L
import           Data.Proxy                       (Proxy(Proxy))
import qualified Data.HashSet                     as HS
import           Safe                             (readMay)
import qualified Text.ParserCombinators.ReadP     as ReadP

import           Instrumentation
import           Prelude.Extended
import           Syntax
import qualified Syntax.Abstract                  as SA
import           Term
import           Term.Impl
import           PrettyPrint                      ((<+>), render, (//>), ($$))
import qualified PrettyPrint                      as PP
import           TypeCheck3.Monad
import           TypeCheck3.Check
import           TypeCheck3.Common
import           TypeCheck3.Elaborate
import           TypeCheck3.Solve

#include "impossible.h"

-- Type checking
------------------------------------------------------------------------

data CheckState t = CheckState
  { _csSolveState     :: !(SolveState t)
  }

L.makeLenses ''CheckState

initCheckState :: (IsTerm t) => IO (CheckState t)
initCheckState = CheckState <$> initSolveState

type CheckM t = TC t (CheckState t)

-- Decls
------------------------------------------------------------------------

checkDecl :: (IsTerm t) => SA.Decl -> CheckM t ()
checkDecl decl = do
  debugBracket_ "checkDecl" (PP.pretty decl) $ atSrcLoc decl $ do
    case decl of
      SA.TypeSig sig      -> checkTypeSig sig
      SA.Postulate sig    -> checkPostulate sig
      SA.Data sig         -> checkData sig
      SA.Record sig       -> checkRecord sig
      SA.DataDef d xs cs  -> checkDataDef d xs cs
      SA.RecDef d xs c fs -> checkRec d xs c fs
      SA.FunDef f clauses -> checkFunDef f clauses

inferExpr
  :: (IsTerm t)
  => Ctx t -> SA.Expr -> CheckM t (Term t, Type t)
inferExpr ctx synT = do
  type_ <- addMetaInCtx ctx set
  t <- checkExpr ctx synT type_
  return (t, type_)

checkExpr
  :: (IsTerm t)
  => Ctx t -> SA.Expr -> Type t -> CheckM t (Term t)
checkExpr ctx synT type_ = do
  debugBracket_ "checkExpr" "" $ do
    (t, constrs) <- elaborate ctx type_ synT
    debug "constraints" $ PP.list <$> mapM prettyM constrs
    mapTC csSolveState $ mapM_ solve constrs
    check ctx t type_
    return t

checkTypeSig :: (IsTerm t) => SA.TypeSig -> CheckM t ()
checkTypeSig (SA.Sig name absType) = do
    type_ <- checkExpr C0 absType set
    addTypeSig name type_

checkPostulate :: (IsTerm t) => SA.TypeSig -> CheckM t ()
checkPostulate (SA.Sig name absType) = do
    type_ <- checkExpr C0 absType set
    addPostulate name type_

checkData :: (IsTerm t) => SA.TypeSig -> CheckM t ()
checkData (SA.Sig name absType) = do
    type_ <- checkExpr C0 absType set
    addData name type_

checkRecord :: (IsTerm t) => SA.TypeSig -> CheckM t ()
checkRecord (SA.Sig name absType) = do
    type_ <- checkExpr C0 absType set
    -- We add it as a postulate first, because we don't know what the
    -- datacon is yet.
    addPostulate name type_

checkDataDef
    :: (IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Names of parameters to the tycon.
    -> [SA.TypeSig]
    -- ^ Types for the data constructors.
    -> CheckM t ()
checkDataDef tyCon tyConPars dataCons = do
    tyConType <- definitionType =<< getDefinition_ tyCon
    (tyConPars0, endType) <- unrollPiWithNames tyConType tyConPars
    let tyConPars' = telToCtx tyConPars0
    definitionallyEqual tyConPars' set endType set
    appliedTyConType <- ctxApp (defName tyCon []) tyConPars'
    mapM_ (checkConstr tyCon tyConPars' appliedTyConType) dataCons

checkConstr
    :: (IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> Ctx (Type t)
    -- ^ Ctx with the parameters of the tycon.
    -> Type t
    -- ^ Tycon applied to the parameters.
    -> SA.TypeSig
    -- ^ Data constructor.
    -> CheckM t ()
checkConstr tyCon tyConPars appliedTyConType (SA.Sig dataCon synDataConType) = do
  atSrcLoc dataCon $ do
    dataConType <- checkExpr tyConPars synDataConType set
    (vsTel, endType) <- unrollPi dataConType
    let vs = telToCtx vsTel
    appliedTyConType' <- ctxWeaken_ vs appliedTyConType
    let ctx = tyConPars <> vs
    definitionallyEqual ctx set appliedTyConType' endType
    addDataCon dataCon tyCon (ctxLength vs) (ctxToTel tyConPars) dataConType

checkRec
    :: (IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Name of the parameters to the tycon.
    -> Name
    -- ^ Name of the data constructor.
    -> [SA.TypeSig]
    -- ^ Fields of the record.
    -> CheckM t ()
checkRec tyCon tyConPars dataCon fields = do
    tyConType <- definitionType =<< getDefinition_ tyCon
    addRecordCon tyCon dataCon
    (tyConParsTel, endType) <- unrollPiWithNames tyConType tyConPars
    let tyConPars' = telToCtx tyConParsTel
    definitionallyEqual tyConPars' set endType set
    fieldsTel <- checkFields tyConPars' fields
    appliedTyConType <- ctxApp (defName tyCon []) tyConPars'
    fieldsTel' <- weaken_ 1 fieldsTel
    addProjections
      tyCon tyConPars' (boundVar "_") (map SA.typeSigName fields)
      fieldsTel'
    let fieldsCtx = telToCtx fieldsTel
    appliedTyConType' <- ctxWeaken_ fieldsCtx appliedTyConType
    addDataCon dataCon tyCon (length fields) (ctxToTel tyConPars') =<< ctxPi fieldsCtx appliedTyConType'

checkFields
    :: forall t. (IsTerm t)
    => Ctx t -> [SA.TypeSig] -> CheckM t (Tel (Type t))
checkFields ctx0 = go C0
  where
    go :: Ctx (Type t) -> [SA.TypeSig] -> CheckM t (Tel (Type t))
    go ctx [] =
        return $ ctxToTel ctx
    go ctx (SA.Sig field synFieldType : fields) = do
        fieldType <- checkExpr (ctx0 <> ctx) synFieldType set
        ctx' <- extendContext ctx (field, fieldType)
        go ctx' fields

addProjections
    :: forall t.
       (IsTerm t)
    => Name
    -- ^ Type constructor.
    -> Ctx (Type t)
    -- ^ A context with the parameters to the type constructor.
    -> Var
    -- ^ Variable referring to the value of type record type itself,
    -- which is the last argument of each projection ("self").  Note
    -- that this variable will have all the context above in scope.
    -> [Name]
    -- ^ Names of the remaining fields.
    -> Tel (Type t)
    -- ^ Telescope holding the types of the next fields, scoped
    -- over the types of the previous fields and the self variable.
    -> CheckM t ()
addProjections tyCon tyConPars self fields0 =
    go $ zipWith Projection' fields0 $ map Field [0,1..]
  where
    go :: [Projection] -> Tel (Type t) -> CheckM t ()
    go fields fieldTypes = case (fields, fieldTypes) of
      ([], T0) ->
        return ()
      (proj : fields', (_, fieldType) :> fieldTypes') -> do
        endType <- (`pi` fieldType) =<< ctxApp (defName tyCon []) tyConPars
        addProjection proj tyCon (ctxToTel tyConPars) endType
        (go fields' <=< instantiate_ fieldTypes') =<< app (Var self) [Proj proj]
      (_, _) -> fatalError "impossible.addProjections: impossible: lengths do not match"

checkFunDef :: (IsTerm t) => Name -> [SA.Clause] -> CheckM t ()
checkFunDef fun synClauses = do
    funDef <- getDefinition_ fun
    case funDef of
      Constant funType (Instantiable (InstFun Open)) -> do
        clauses <- mapM (checkClause fun funType) synClauses
        inv <- checkInvertibility clauses
        addClauses fun inv
      Constant _ Postulate -> do
        typeError $ "Cannot give body to postulate" <+> PP.pretty fun
      _ -> do
        __IMPOSSIBLE__

checkClause
  :: (IsTerm t)
  => Name -> Closed (Type t)
  -> SA.Clause
  -> CheckM t (Closed (Clause t))
checkClause fun funType (SA.Clause synPats synClauseBody) = do
  (ctx, pats, _, clauseType) <- checkPatterns fun synPats funType
  let msg = do
        ctxDoc <- prettyM ctx
        return $ "context:" //> ctxDoc
  debugBracket "checkClause" msg $ do
    clauseBody <- checkExpr ctx synClauseBody clauseType
    return $ Clause pats clauseBody

checkPatterns
  :: (IsTerm t)
  => Name
  -> [SA.Pattern]
  -> Type t
  -- ^ Type of the clause that has the given 'SA.Pattern's in front.
  -> CheckM t (Ctx (Type t), [Pattern], [Term t], Type t)
  -- ^ A context into the internal variables, list of internal patterns,
  -- a list of terms produced by their bindings, and the type of the
  -- clause body (scoped over the pattern variables).
checkPatterns _ [] type_ =
    return (C0, [], [], type_)
checkPatterns funName (synPat : synPats) type0 = atSrcLoc synPat $ do
  -- TODO this can be a soft match, like `matchPi'.  I just need to
  -- carry the context around.
  typeView <- whnfView type0
  case typeView of
    Pi dom cod -> do
      (ctx, pat, patVar) <- checkPattern funName synPat dom
      cod'  <- ctxWeaken 1 ctx cod
      cod'' <- instantiate_ cod' patVar
      (ctx', pats, patsVars, bodyType) <- checkPatterns funName synPats cod''
      patVar' <- ctxWeaken_ ctx' patVar
      return (ctx <> ctx', pat : pats, patVar' : patsVars, bodyType)
    _ -> do
      checkError $ ExpectingPi type0

checkPattern
    :: (IsTerm t)
    => Name
    -> SA.Pattern
    -> Type t
    -- ^ Type of the matched thing.
    -> CheckM t (Ctx (Type t), Pattern, Term t)
    -- ^ The context, the internal 'Pattern', and a 'Term' containing
    -- the term produced by it.
checkPattern funName synPat type_ = case synPat of
    SA.VarP name -> do
      v <- var $ boundVar name
      return (ctxSingleton name type_, VarP, v)
    SA.WildP _ -> do
      v <- var $ boundVar "_"
      return (ctxSingleton "_" type_, VarP, v)
    SA.ConP dataCon synPats -> do
      DataCon tyCon _ tyConParsTel dataConType <- getDefinition_ dataCon
      typeConDef <- getDefinition_ tyCon
      case typeConDef of
        Constant _ (Data _)     -> return ()
        Constant _ (Record _ _) -> checkError $ PatternMatchOnRecord synPat tyCon
        _                       -> do doc <- prettyM typeConDef
                                      fatalError $ "impossible.checkPattern " ++ render doc
      typeView <- whnfView type_
      -- TODO this can be a soft match, like `matchTyCon'
      case typeView of
        App (Def (DKName tyCon')) tyConArgs0 | tyCon == tyCon' -> do
          let Just tyConArgs = mapM isApply tyConArgs0
          dataConTypeNoPars <- telDischarge tyConParsTel dataConType tyConArgs
          (ctx, pats, patsVars, _) <- checkPatterns funName synPats dataConTypeNoPars
          t <- con dataCon patsVars
          return (ctx, ConP dataCon pats, t)
        _ -> do
          checkError $ ExpectingTyCon tyCon type_

-- Bringing everything together
------------------------------------------------------------------------

-- Checking programs
--------------------

type TCState' t = TCState t (CheckState t)

emptyTCState' :: (forall t. (IsTerm t) => TCState' t -> IO a) -> IO a
emptyTCState' ret = do
  dummyS :: CheckState Simple <- initCheckState
  ret $ initTCState dummyS

checkProgram
  :: [SA.Decl]
  -> (forall t. (IsTerm t) => (TCState' t, Maybe PP.Doc) -> IO a) -> IO a
checkProgram decls ret = do
  tt <- confTermType <$> readConf
  case tt of
    "S"   -> checkProgram' (Proxy :: Proxy Simple) decls ret
    "GR"  -> checkProgram' (Proxy :: Proxy GraphReduce) decls ret
    -- "GRS" -> checkProgram' (Proxy :: Proxy GraphReduceSub) decls ret
    "GRU" -> checkProgram' (Proxy :: Proxy GraphReduceUnpack) decls ret
    "H"   -> checkProgram' (Proxy :: Proxy Hashed) decls ret
    type_ -> emptyTCState' $ \dummyS -> do
      ret (dummyS, Just ("Invalid term type" <+> PP.text type_))

checkProgram'
    :: forall t a. (IsTerm t)
    => Proxy t -> [SA.Decl] -> ((TCState' t, Maybe PP.Doc) -> IO a) -> IO a
checkProgram' _ decls0 ret = do
    quiet <- confQuiet <$> readConf
    unless quiet $ do
      drawLine
      putStrLn "-- Checking declarations"
      drawLine
    s <- initCheckState
    ret =<< goDecls (initTCState s) decls0
  where
    goDecls :: TCState' t -> [SA.Decl] -> IO (TCState' t, Maybe PP.Doc)
    goDecls ts [] = do
      (ts,) <$> checkState ts
    goDecls ts (decl : decls) = do
      quiet <- confQuiet <$> readConf
      unless quiet $ do
        putStrLn $ render decl
        let separate = case decl of
              SA.TypeSig (SA.Sig n _) -> case decls of
                SA.FunDef n' _     : _  -> not $ n == n'
                SA.DataDef n' _ _  : _  -> not $ n == n'
                SA.RecDef n' _ _ _ : _  -> not $ n == n'
                []                     -> False
                _                      -> True
              _ ->
                not $ null decls
        when separate $ putStrLn ""
      (mbErr, ts') <- runTC ts $ checkDecl decl
      case mbErr of
        Left err -> return (ts', Just err)
        Right () -> goDecls ts' decls

    -- TODO change for this to work in TC
    checkState :: TCState' t -> IO (Maybe PP.Doc)
    checkState ts = do
      let sig = tsSignature ts
      unsolvedMvs <- runTermM sig $ metas sig
      quiet <- confQuiet <$> readConf
      unless quiet $ do
        mvNoSummary <- confNoMetasSummary <$> readConf
        mvReport <- confMetasReport <$> readConf
        mvOnlyUnsolved <- confMetasOnlyUnsolved <$> readConf
        when (not mvNoSummary || mvReport) $ do
          let catInsts xs = [i | i@Inst{} <- xs]
          let solvedMvs = catInsts $ map (sigGetMetaInst sig) $ sigDefinedMetas sig
          let isInst Inst{} = True
              isInst Open   = False
          drawLine
          putStrLn $ "-- Solved Metas: " ++ show (length solvedMvs)
          putStrLn $ "-- Unsolved Metas: " ++ show (HS.size unsolvedMvs)
          when mvReport $ do
            drawLine
            let mvsTypes = map (\mv -> (mv, sigGetMetaType sig mv)) $ sigDefinedMetas sig
            forM_ (sortBy (comparing fst) $ mvsTypes) $ \(mv, mvType) -> do
              let mbMvb = sigGetMetaInst sig mv
              when (not (isInst mbMvb) || not mvOnlyUnsolved) $ do
                mvTypeDoc <- runTermM sig $ prettyM mvType
                putStrLn $ render $
                  PP.pretty mv <+> PP.parens (PP.pretty (srcLoc mv)) <+> ":" //> mvTypeDoc
                when (not mvOnlyUnsolved) $ do
                  mvBody <- case mbMvb of
                    Open   -> return "?"
                    Inst{} -> runTermM sig $ prettyM =<< metaInstToTerm mbMvb
                  putStrLn $ render $ PP.pretty mv <+> "=" <+> PP.nest 2 mvBody
                putStrLn ""
        noProblemsSummary <- confNoProblemsSummary <$> readConf
        problemsReport <- confProblemsReport <$> readConf
        when (not noProblemsSummary || problemsReport) $  do
          drawLine
          putStrLn . render =<< runTermM sig (prettyM (tsState ts ^. csSolveState))
        drawLine
      return $ if HS.null unsolvedMvs
               then Nothing
               else Just $ "Unsolved metas: " <+> PP.pretty (HS.toList unsolvedMvs)

    drawLine =
      putStrLn "------------------------------------------------------------------------"

-- Commands
------------------------------------------------------------------------

data Command
  = TypeOf SA.Expr
  | Normalize SA.Expr
  | ShowConstraints
  | ShowMeta Meta
  | Help
  deriving (Eq, Show)

parseCommand :: TCState' t -> String -> Either PP.Doc Command
parseCommand ts s0 = runReadP $
  (do void $ ReadP.string ":t " <|> ReadP.string ":type "
      return (\s -> TypeOf <$> parseAndScopeCheck s)) <|>
  (do void $ ReadP.string ":n " <|> ReadP.string ":normalize "
      return (\s -> Normalize <$> parseAndScopeCheck s)) <|>
  (do void $ ReadP.string ":c" <|> ReadP.string ":constraints"
      ReadP.eof
      return (\_ -> Right ShowConstraints)) <|>
  (do void $ ReadP.string ":mv" <|> ReadP.string ":metavar "
      return (\s -> ShowMeta <$> parseMeta s)) <|>
  (do void $ ReadP.string ":h" <|> ReadP.string ":help"
      ReadP.eof
      return (\_ -> Right Help))
  where
    scope = sigToScope $ tsSignature ts

    parseAndScopeCheck = parseExpr >=> SA.scopeCheckExpr scope

    parseMeta s =
      case readMay s of
        Just mv ->
          Right Meta{metaId = mv, metaSrcLoc = SA.noSrcLoc}
        _ ->
          Left $ "Invalid metavar id" <+> PP.text s

    runReadP :: ReadP.ReadP (String -> Either PP.Doc Command) -> Either PP.Doc Command
    runReadP p = case ReadP.readP_to_S p s0 of
      []            -> Left "Unrecognised command"
      ((f, s') : _) -> f s'

runCommand :: (IsTerm t) => TCState' t -> Command -> IO (PP.Doc, TCState' t)
runCommand ts cmd =
  case cmd of
    TypeOf synT -> runTC' $ do
      (_, type_) <- inferExpr C0 synT
      typeDoc <- prettyM type_
      return $ "type:" //> typeDoc
    Normalize synT -> runTC' $ do
      (t, type_) <- inferExpr C0 synT
      typeDoc <- prettyM type_
      tDoc <- prettyM t
      return $
        "type:" //> typeDoc $$
        "term:" //> tDoc
    ShowConstraints -> runTC' $ do
      prettyM =<< L.use csSolveState
    ShowMeta mv -> runTC' $ do
      mvType <- getMetaType mv
      mbMvBody <- getMetaInst mv
      mvTypeDoc <- prettyM mvType
      mvBodyDoc <- prettyM mbMvBody
      return $
        PP.pretty mv <+> ":" <+> mvTypeDoc $$
        PP.pretty mv <+> "=" <+> mvBodyDoc
    Help -> runTC' $ do
      return $
        ":t [EXPR], :type [EXPR]\t\tTypecheck an expression" $$
        ":n [EXPR], :normalize [EXPR]\tTypecheck and normalize an expression" $$
        ":c, :constraints\t\tShow unsolved constraints" $$
        ":mv [ID], metavar [ID]\t\tDisplay type and body (if instantiated) of a metavariable" $$
        ":h, :help\t\t\tDisplay this message"
  where
    runTC' m = do
      (mbErr, _) <- runTC ts m
      let doc = case mbErr of
                  Left err   -> "Error:" //> err
                  Right doc0 -> doc0
      return (doc, ts)
