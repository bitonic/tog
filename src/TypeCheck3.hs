{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
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

import           Prelude                          hiding (abs, pi)

import           Control.Lens                     ((^.))
import qualified Control.Lens                     as L
import           Data.Proxy                       (Proxy(Proxy))
import qualified Data.HashSet                     as HS
import qualified Data.HashMap.Strict              as HMS
import           Safe                             (readMay)
import qualified Text.ParserCombinators.ReadP     as ReadP

import           Conf
import           Prelude.Extended
import           Syntax
import qualified Syntax.Internal                  as SI
import           Term
import qualified Term.Signature                   as Sig
import qualified Term.Context                     as Ctx
import qualified Term.Telescope                   as Tel
import           Term.Impl
import           PrettyPrint                      ((<+>), render, (//>), ($$))
import qualified PrettyPrint                      as PP
import           TypeCheck3.Monad
import           TypeCheck3.Check
import           TypeCheck3.Common
import           TypeCheck3.Elaborate
import           TypeCheck3.Solve

-- Type checking
------------------------------------------------------------------------

data CheckState t = CheckState
  { _csSolveState     :: !(SolveState t)
  , _csElaborateState :: !(ElaborateState t)
  }

L.makeLenses ''CheckState

initCheckState :: (IsTerm t) => IO (CheckState t)
initCheckState = CheckState <$> initSolveState <*> initElaborateState

type CheckM t = TC t (CheckState t)

-- Decls
------------------------------------------------------------------------

checkDecl :: (IsTerm t) => SI.Decl -> CheckM t ()
checkDecl decl = do
  debugSection_ "checkDecl" (PP.pretty decl) $ atSrcLoc decl $ do
    case decl of
      SI.TypeSig sig      -> checkTypeSig sig
      SI.Postulate sig    -> checkPostulate sig
      SI.DataDef d xs cs  -> checkData d xs cs
      SI.RecDef d xs c fs -> checkRec d xs c fs
      SI.FunDef f clauses -> checkFunDef f clauses

inferExpr
  :: (IsTerm t)
  => Ctx t -> SI.Expr -> CheckM t (Term t, Type t)
inferExpr ctx synT = do
  type_ <- addMetaVarInCtx ctx set
  t <- checkExpr ctx synT type_
  return (t, type_)

checkExpr
  :: (IsTerm t)
  => Ctx t -> SI.Expr -> Type t -> CheckM t (Term t)
checkExpr ctx synT type_ = do
  debugBracket_ "checkExpr" "" $ do
    (t, constrs) <- mapTC csElaborateState $ elaborate ctx type_ synT
    debug "constraints" $ PP.list <$> mapM prettyM constrs
    mapTC csSolveState $ mapM_ solve constrs
    check ctx t type_
    return t

checkTypeSig :: (IsTerm t) => SI.TypeSig -> CheckM t ()
checkTypeSig (SI.Sig name absType) = do
    type_ <- checkExpr Ctx.Empty absType set
    addConstant name TypeSig type_

checkPostulate :: (IsTerm t) => SI.TypeSig -> CheckM t ()
checkPostulate (SI.Sig name absType) = do
    type_ <- checkExpr Ctx.Empty absType set
    addConstant name Postulate type_

checkData
    :: (IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Names of parameters to the tycon.
    -> [SI.TypeSig]
    -- ^ Types for the data constructors.
    -> CheckM t ()
checkData tyCon tyConPars dataCons = do
    tyConType <- definitionType =<< getDefinition tyCon
    addConstant tyCon (Data []) tyConType
    (tyConPars', endType) <- unrollPiWithNames tyConType tyConPars
    definitionallyEqual tyConPars' set endType set
    appliedTyConType <- Ctx.app (def tyCon []) tyConPars'
    mapM_ (checkConstr tyCon tyConPars' appliedTyConType) dataCons

checkConstr
    :: (IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> Ctx (Type t)
    -- ^ Ctx with the parameters of the tycon.
    -> Type t
    -- ^ Tycon applied to the parameters.
    -> SI.TypeSig
    -- ^ Data constructor.
    -> CheckM t ()
checkConstr tyCon tyConPars appliedTyConType (SI.Sig dataCon synDataConType) = do
  atSrcLoc dataCon $ do
    dataConType <- checkExpr tyConPars synDataConType set
    (vs, endType) <- unrollPi dataConType
    appliedTyConType' <- Ctx.weaken_ vs appliedTyConType
    let ctx = tyConPars Ctx.++ vs
    definitionallyEqual ctx set appliedTyConType' endType
    addDataCon dataCon tyCon (Ctx.length vs) (Tel.tel tyConPars) dataConType

checkRec
    :: (IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Name of the parameters to the tycon.
    -> Name
    -- ^ Name of the data constructor.
    -> [SI.TypeSig]
    -- ^ Fields of the record.
    -> CheckM t ()
checkRec tyCon tyConPars dataCon fields = do
    tyConType <- definitionType =<< getDefinition tyCon
    addConstant tyCon (Record dataCon []) tyConType
    (tyConPars', endType) <- unrollPiWithNames tyConType tyConPars
    definitionallyEqual tyConPars' set endType set
    fieldsTel <- checkFields tyConPars' fields
    appliedTyConType <- Ctx.app (def tyCon []) tyConPars'
    fieldsTel' <- weaken_ 1 fieldsTel
    addProjections
      tyCon tyConPars' (boundVar "_") (map SI.typeSigName fields)
      fieldsTel'
    let fieldsCtx = Tel.unTel fieldsTel
    appliedTyConType' <- Ctx.weaken_ fieldsCtx appliedTyConType
    addDataCon dataCon tyCon (length fields) (Tel.tel tyConPars') =<< Ctx.pi fieldsCtx appliedTyConType'

checkFields
    :: forall t. (IsTerm t)
    => Ctx t -> [SI.TypeSig] -> CheckM t (Tel.Tel (Type t))
checkFields ctx0 = go Ctx.Empty
  where
    go :: Ctx.Ctx (Type t) -> [SI.TypeSig] -> CheckM t (Tel.Tel (Type t))
    go ctx [] =
        return $ Tel.tel ctx
    go ctx (SI.Sig field synFieldType : fields) = do
        fieldType <- checkExpr (ctx0 Ctx.++ ctx) synFieldType set
        ctx' <- extendContext ctx (field, fieldType)
        go ctx' fields

addProjections
    :: (IsTerm t)
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
    -> Tel.Tel (Type t)
    -- ^ Telescope holding the types of the next fields, scoped
    -- over the types of the previous fields and the self variable.
    -> CheckM t ()
addProjections tyCon tyConPars self fields0 =
    go $ zipWith Projection' fields0 $ map Field [0,1..]
  where
    go fields fieldTypes = case (fields, fieldTypes) of
      ([], Tel.Empty) ->
        return ()
      (proj : fields', Tel.Cons (_, fieldType) fieldTypes') -> do
        endType <- (`pi` fieldType) =<< Ctx.app (def tyCon []) tyConPars
        addProjection proj tyCon (Tel.tel tyConPars) endType
        (go fields' <=< instantiate_ fieldTypes') =<< app (Var self) [Proj proj]
      (_, _) -> fatalError "impossible.addProjections: impossible: lengths do not match"

checkFunDef :: (IsTerm t) => Name -> [SI.Clause] -> CheckM t ()
checkFunDef fun synClauses = do
    funDef <- getDefinition fun
    case funDef of
      Constant TypeSig funType -> do
        clauses <- mapM (checkClause fun funType) synClauses
        inv <- checkInvertibility clauses
        addClauses fun inv
      Constant Postulate _ -> do
        typeError $ "Cannot give body to postulate" <+> PP.pretty fun
      _ -> do
        fatalError "impossible.checkFunDef"

checkClause
  :: (IsTerm t)
  => Name -> Closed (Type t)
  -> SI.Clause
  -> CheckM t (Closed (Clause t))
checkClause fun funType (SI.Clause synPats synClauseBody) = do
  (ctx, pats, _, clauseType) <- checkPatterns fun synPats funType
  let msg = do
        ctxDoc <- prettyM ctx
        return $ "context:" //> ctxDoc
  debugBracket "checkClause" msg $ do
    clauseBody <- checkExpr ctx synClauseBody clauseType
    -- This is an optimization: we want to remove as many MetaVars
    -- as possible so that we'll avoid recomputing things.
    -- TODO generalize this to everything which adds a term.
    clauseBody' <- instantiateMetaVars clauseBody
    return $ Clause pats clauseBody'

checkPatterns
  :: (IsTerm t)
  => Name
  -> [SI.Pattern]
  -> Type t
  -- ^ Type of the clause that has the given 'SI.Pattern's in front.
  -> CheckM t (Ctx (Type t), [Pattern], [Term t], Type t)
  -- ^ A context into the internal variables, list of internal patterns,
  -- a list of terms produced by their bindings, and the type of the
  -- clause body (scoped over the pattern variables).
checkPatterns _ [] type_ =
    return (Ctx.Empty, [], [], type_)
checkPatterns funName (synPat : synPats) type0 = atSrcLoc synPat $ do
  -- TODO this can be a soft match, like `matchPi'.  I just need to
  -- carry the context around.
  typeView <- whnfView type0
  case typeView of
    Pi dom cod -> do
      (ctx, pat, patVar) <- checkPattern funName synPat dom
      cod'  <- Ctx.weaken 1 ctx cod
      cod'' <- instantiate_ cod' patVar
      (ctx', pats, patsVars, bodyType) <- checkPatterns funName synPats cod''
      patVar' <- Ctx.weaken_ ctx' patVar
      return (ctx Ctx.++ ctx', pat : pats, patVar' : patsVars, bodyType)
    _ -> do
      checkError $ ExpectingPi type0

checkPattern
    :: (IsTerm t)
    => Name
    -> SI.Pattern
    -> Type t
    -- ^ Type of the matched thing.
    -> CheckM t (Ctx (Type t), Pattern, Term t)
    -- ^ The context, the internal 'Pattern', and a 'Term' containing
    -- the term produced by it.
checkPattern funName synPat type_ = case synPat of
    SI.VarP name -> do
      v <- var $ boundVar name
      return (Ctx.singleton name type_, VarP, v)
    SI.WildP _ -> do
      v <- var $ boundVar "_"
      return (Ctx.singleton "_" type_, VarP, v)
    SI.ConP dataCon synPats -> do
      DataCon tyCon _ tyConParsTel dataConType <- getDefinition dataCon
      typeConDef <- getDefinition tyCon
      case typeConDef of
        Constant (Data _)     _ -> return ()
        Constant (Record _ _) _ -> checkError $ PatternMatchOnRecord synPat tyCon
        _                       -> do doc <- prettyM typeConDef
                                      fatalError $ "impossible.checkPattern " ++ render doc
      typeView <- whnfView type_
      -- TODO this can be a soft match, like `matchTyCon'
      case typeView of
        App (Def tyCon') tyConArgs0 | tyCon == tyCon' -> do
          let Just tyConArgs = mapM isApply tyConArgs0
          dataConTypeNoPars <- Tel.discharge tyConParsTel dataConType tyConArgs
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
  :: [SI.Decl]
  -> (forall t. (IsTerm t) => (TCState' t, Maybe PP.Doc) -> IO a) -> IO a
checkProgram decls ret = do
  tt <- confTermType <$> readConf
  case tt of
    "S"   -> checkProgram' (Proxy :: Proxy Simple) decls ret
    "GR"  -> checkProgram' (Proxy :: Proxy GraphReduce) decls ret
    "GRS" -> checkProgram' (Proxy :: Proxy GraphReduceSub) decls ret
    "GRU" -> checkProgram' (Proxy :: Proxy GraphReduceUnpack) decls ret
    "H"   -> checkProgram' (Proxy :: Proxy Hashed) decls ret
    type_ -> emptyTCState' $ \dummyS -> do
      ret (dummyS, Just ("Invalid term type" <+> PP.text type_))

checkProgram'
    :: forall t a. (IsTerm t)
    => Proxy t -> [SI.Decl] -> ((TCState' t, Maybe PP.Doc) -> IO a) -> IO a
checkProgram' _ decls0 ret = do
    quiet <- confQuiet <$> readConf
    unless quiet $ do
      drawLine
      putStrLn "-- Checking declarations"
      drawLine
    s <- initCheckState
    ret =<< goDecls (initTCState s) decls0
  where
    goDecls :: TCState' t -> [SI.Decl] -> IO (TCState' t, Maybe PP.Doc)
    goDecls ts [] = do
      (ts,) <$> checkState ts
    goDecls ts (decl : decls) = do
      quiet <- confQuiet <$> readConf
      unless quiet $ do
        putStrLn $ render decl
        let separate = case decl of
              SI.TypeSig (SI.Sig n _) -> case decls of
                SI.FunDef n' _     : _  -> not $ n == n'
                SI.DataDef n' _ _  : _  -> not $ n == n'
                SI.RecDef n' _ _ _ : _  -> not $ n == n'
                []                     -> False
                _                      -> True
              _ ->
                not $ null decls
        when separate $ putStrLn ""
      (mbErr, ts') <- runTC_ ts $ checkDecl decl
      case mbErr of
        Left err -> return (ts', Just err)
        Right () -> goDecls ts' decls

    -- TODO change for this to work in TC
    checkState :: TCState' t -> IO (Maybe PP.Doc)
    checkState ts = do
      let sig = tsSignature ts
      unsolvedMvs <- runTermM sig $ metaVars sig
      quiet <- confQuiet <$> readConf
      unless quiet $ do
        mvNoSummary <- confNoMetaVarsSummary <$> readConf
        mvReport <- confMetaVarsReport <$> readConf
        mvOnlyUnsolved <- confMetaVarsOnlyUnsolved <$> readConf
        when (not mvNoSummary || mvReport) $ do
          let solvedMvs   = HS.fromList $ HMS.keys $ Sig.metaVarsBodies sig
          drawLine
          putStrLn $ "-- Solved MetaVars: " ++ show (HS.size solvedMvs)
          putStrLn $ "-- Unsolved MetaVars: " ++ show (HS.size unsolvedMvs)
          when mvReport $ do
            drawLine
            let mvsTypes = Sig.metaVarsTypes sig
            forM_ (sortBy (comparing fst) $ HMS.toList mvsTypes) $ \(mv, mvType) -> do
              let mbBody = Sig.getMetaVarBody sig mv
              when (not (isJust mbBody) || not mvOnlyUnsolved) $ do
                mvTypeDoc <- runTermM sig $ prettyM mvType
                putStrLn $ render $
                  PP.pretty mv <+> PP.parens (PP.pretty (mvSrcLoc mv)) <+> ":" //> mvTypeDoc
                when (not mvOnlyUnsolved) $ do
                  mvBody <- case mbBody of
                    Nothing      -> return "?"
                    Just mvBody0 -> runTermM sig $ prettyM mvBody0
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
  = TypeOf SI.Expr
  | Normalize SI.Expr
  | ShowConstraints
  | ShowMeta MetaVar
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
      return (\s -> ShowMeta <$> parseMetaVar s)) <|>
  (do void $ ReadP.string ":h" <|> ReadP.string ":help"
      ReadP.eof
      return (\_ -> Right Help))
  where
    scope = Sig.toScope $ tsSignature ts

    parseAndScopeCheck = parseExpr >=> SI.scopeCheckExpr scope

    parseMetaVar s =
      case readMay s of
        Just mv ->
          Right MetaVar{mvId = mv, mvSrcLoc = SI.noSrcLoc}
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
      (_, type_) <- inferExpr Ctx.Empty synT
      typeDoc <- prettyM type_
      return $ "type:" //> typeDoc
    Normalize synT -> runTC' $ do
      (t, type_) <- inferExpr Ctx.Empty synT
      typeDoc <- prettyM type_
      tDoc <- prettyM t
      return $
        "type:" //> typeDoc $$
        "term:" //> tDoc
    ShowConstraints -> runTC' $ do
      prettyM =<< L.use csSolveState
    ShowMeta mv -> runTC' $ do
      mvType <- getMetaVarType mv
      mbMvBody <- getMetaVarBody mv
      mvTypeDoc <- prettyM mvType
      mvBodyDoc <- case mbMvBody of
        Nothing   -> return "?"
        Just body -> prettyM body
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
      (mbErr, _) <- runTC (TCConf True False []) ts m
      let doc = case mbErr of
                  Left err   -> "Error:" //> err
                  Right doc0 -> doc0
      return (doc, ts)
