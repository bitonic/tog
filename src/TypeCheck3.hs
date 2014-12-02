{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
module TypeCheck3
  ( -- * Program checking
    checkProgram
  ) where
  --   -- * Interactive mode
  -- , Command
  -- , parseCommand
  -- , runCommand
  -- ) where

import qualified Control.Lens                     as L
import           Data.Proxy                       (Proxy(Proxy))
import qualified Data.HashSet                     as HS
-- import           Safe                             (readMay)
-- import qualified Text.ParserCombinators.ReadP     as ReadP

import           Instrumentation
import           Prelude.Extended
import           Syntax
import qualified Syntax.Abstract                  as SA
import           Term
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

type CheckM t = TC t (ElabEnv t) (CheckState t)
type CCheckM t = forall b. CheckM t b -> CheckM t b

-- Decls
------------------------------------------------------------------------

checkDecl
  :: (IsTerm t)
  => ElabEnv t
  -> SA.Decl
  -> TC t r (CheckState t) (ElabEnv t)
checkDecl env decl = do
  let cont = ask
  magnifyTC (const env) $ do
    debugBracket_ "checkDecl" (PP.pretty decl) $ atSrcLoc decl $ do
      case decl of
        SA.TypeSig sig      -> checkTypeSig sig cont
        SA.Postulate sig    -> checkPostulate sig cont
        SA.Data sig         -> checkData sig cont
        SA.Record sig       -> checkRecord sig cont
        SA.DataDef d xs cs  -> checkDataDef d xs cs cont
        SA.RecDef d xs c fs -> checkRecDef d xs c fs cont
        SA.FunDef f clauses -> checkFunDef f clauses cont

checkDecls :: (IsTerm t) => ElabEnv t -> [SA.Decl] -> TC t r (CheckState t) (ElabEnv t)
checkDecls env [] = do
  return env
checkDecls env (decl : decls) = do
  env' <- checkDecl env decl
  checkDecls env' decls

addConstantAndOpen
  :: (IsTerm t)
  => (Name -> Tel t -> Type t -> CheckM t ())
  -> Name
  -> Type t
  -> CCheckM t
addConstantAndOpen f name type_ cont = do
  tel <- asks elabEnvTel
  f name tel type_
  openDefinitionInEnv_ name $ \_ -> cont

checkExpr
  :: (IsTerm t)
  => SA.Expr -> Type t -> CheckM t (Term t)
checkExpr synT type_ = do
  let msg = do
        typeDoc <- prettyM type_
        return $
          "type:" //> typeDoc $$
          "term:" //> PP.pretty synT
  debugBracket "checkExpr" msg $ do
    (t, constrs) <- elaborate type_ synT
    zoomTC csSolveState $ mapM_ solve constrs
    ctx <- asks elabEnvCtx
    check ctx t type_
    return t

checkTypeSig :: (IsTerm t) => SA.TypeSig -> CCheckM t
checkTypeSig (SA.Sig name absType) cont = do
    type_ <- checkExpr absType set
    addConstantAndOpen addTypeSig name type_ cont

checkPostulate :: (IsTerm t) => SA.TypeSig -> CCheckM t
checkPostulate (SA.Sig name absType) cont = do
    type_ <- checkExpr absType set
    addConstantAndOpen addPostulate name type_ cont

checkData :: (IsTerm t) => SA.TypeSig -> CCheckM t
checkData (SA.Sig name absType) cont = do
    type_ <- checkExpr absType set
    -- Check that at the end of the type there is a 'Set'
    (tel, endType) <- unrollPi type_
    extendEnv (telToCtx tel) $ do
      ctx <- asks elabEnvCtx
      definitionallyEqual ctx set endType set
    addConstantAndOpen addData name type_ cont

checkRecord :: (IsTerm t) => SA.TypeSig -> CCheckM t
checkRecord (SA.Sig name absType) cont = do
    type_ <- checkExpr absType set
    -- Check that at the end of the type there is a 'Set'
    (tel, endType) <- unrollPi type_
    extendEnv (telToCtx tel) $ do
      ctx <- asks elabEnvCtx
      definitionallyEqual ctx set endType set
    -- We add it as a postulate first, because we don't know what the
    -- datacon is yet.
    addConstantAndOpen addPostulate name type_ cont

checkDataDef
    :: (IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Names of parameters to the tycon.
    -> [SA.TypeSig]
    -- ^ Types for the data constructors.
    -> CCheckM t
checkDataDef tyCon0 tyConParsNames dataCons cont = do
  -- The type constructor must already be defined, and opened
  (tyCon, _) <- getOpenedDefinition tyCon0
  tyConType <- definitionType =<< getDefinition tyCon
  (tyConPars, _) <- unrollPiWithNames tyConType tyConParsNames
  -- We check the data constructor types under the type parameters of
  -- the type constructor
  dataConsTypes <- extendEnv (telToCtx tyConPars) $ do
    -- We need to weaken the opened tyCon name -- to weaken its arguments.
    tyCon' <- applySubst tyCon $ subWeaken (telLength tyConPars) subId
    appliedTyConType <- telApp (def tyCon' []) tyConPars
    mapM (checkDataCon appliedTyConType) dataCons
  -- Now we repeatedly add the data constructors.
  let go [] cont' = do
        cont'
      go ((dataCon, dataConArgs, dataConType) : dataConsTypes') cont' = do
        addDataCon dataCon tyCon dataConArgs $ Contextual tyConPars dataConType
        openDefinitionInEnv_ dataCon $ \_ -> go dataConsTypes' cont'
  go dataConsTypes cont

checkDataCon
    :: (IsTerm t)
    => Type t
    -- ^ Tycon applied to the parameters.
    -> SA.TypeSig
    -- ^ Data constructor type
    -> CheckM t (Name, Natural, Type t)
    -- ^ Name of the datacon, number of arguments and type of the data
    -- constructor, scoped over the parameters of the data type.
checkDataCon appliedTyConType (SA.Sig dataCon synDataConType) = do
  atSrcLoc dataCon $ do
    dataConType <- checkExpr synDataConType set
    (vsTel, endType) <- unrollPi dataConType
    extendEnv (telToCtx vsTel) $ do
      appliedTyConType' <- weaken_ (telLength vsTel) appliedTyConType
      ctx <- asks elabEnvCtx
      definitionallyEqual ctx set appliedTyConType' endType
    return (dataCon, telLength vsTel, dataConType)

checkRecDef
    :: (IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Name of the parameters to the tycon.
    -> Name
    -- ^ Name of the data constructor.
    -> [SA.TypeSig]
    -- ^ Fields of the record.
    -> CCheckM t
checkRecDef tyCon0 tyConPars dataCon fields cont = do
  -- The tyCon must already be opened (and in the same module)
  (tyCon, _) <- getOpenedDefinition tyCon0
  tyConType <- definitionType =<< getDefinition tyCon
  -- Add the constructor name to the tyCon
  addRecordCon tyCon dataCon
  -- Enter a context with the arguments to the tyCon in scope
  (tyConParsTel, _) <- unrollPiWithNames tyConType tyConPars
  fieldsTel <- extendEnv (telToCtx tyConParsTel) $ checkFields fields
  fieldsTel' <- weaken_ 1 fieldsTel
  tyCon' <- weaken_ (telLength tyConParsTel) tyCon
  appliedTyConType <- telApp (def tyCon' []) tyConParsTel
  addProjections tyCon tyConParsTel (boundVar "_") (map SA.typeSigName fields) fieldsTel' $ do
    dataConType <- telPi fieldsTel =<< weaken_ (telLength fieldsTel) appliedTyConType
    addDataCon dataCon tyCon (length fields) $ Contextual tyConParsTel dataConType
    openDefinitionInEnv_ dataCon $ \_ ->  cont

checkFields
    :: forall t. (IsTerm t)
    => [SA.TypeSig] -> CheckM t (Tel (Type t))
checkFields = go C0
  where
    go :: Ctx (Type t) -> [SA.TypeSig] -> CheckM t (Tel (Type t))
    go ctx [] =
        return $ ctxToTel ctx
    go ctx (SA.Sig field synFieldType : fields) = do
        fieldType <- extendEnv ctx $ checkExpr synFieldType set
        go (ctx :< (field, fieldType)) fields

addProjections
    :: forall t.
       (IsTerm t)
    => Opened Name t
    -- ^ Type constructor.
    -> Tel (Type t)
    -- ^ Arguments to the type constructors
    -> Var
    -- ^ Variable referring to the value of type record type itself,
    -- which is the last argument of each projection ("self").  Note
    -- that this variable will have all the context above in scope.
    -> [Name]
    -- ^ Names of the remaining fields.
    -> Tel (Type t)
    -- ^ Telescope holding the types of the next fields, scoped
    -- over the types of the previous fields and the self variable.
    -> CCheckM t
addProjections tyCon tyConPars self fields0 fieldTypes0 cont = do
    appliedTyCon <- telApp (def tyCon []) tyConPars

    let go [] T0 = do
          cont
        go (proj : fields') ((_, fieldType) :> fieldTypes') = do
          endType <- pi appliedTyCon fieldType
          addProjection proj tyCon $ Contextual tyConPars endType
          openDefinitionInEnv_ (pName proj) $ \openedProj -> do
            projected <- app (Var self) [Proj (first (const proj) openedProj)]
            go fields' =<< instantiate_ fieldTypes' projected
        go _ _ = do
          __IMPOSSIBLE__

    go (zipWith Projection' fields0 $ map Field [0,1..]) fieldTypes0

checkFunDef
  :: (IsTerm t) => Name -> [SA.Clause] -> CCheckM t
checkFunDef fun0 synClauses cont = do
    (fun, funDef) <- getOpenedDefinition fun0
    case funDef of
      Constant funType (Function Open) -> do
        clauses <- mapM (checkClause funType) synClauses
        inv <- checkInvertibility clauses
        -- We don't need to extend the environment, because the function
        -- definition is already open
        addClauses fun inv
        cont
      Constant _ Postulate -> do
        funDoc <- prettyM fun
        typeError $ "Cannot give body to postulate" <+> funDoc
      _ -> do
        __IMPOSSIBLE__

checkClause
  :: (IsTerm t)
  => Closed (Type t)
  -> SA.Clause
  -> CheckM t (Closed (Clause t))
checkClause funType (SA.Clause synPats synClauseBody wheres) = do
  -- We check the patterns, and start a new block with the context that
  -- the patterns have left us with.
  checkPatterns synPats funType $ \pats clauseType -> startBlock $ do
    let msg = do
          ctxDoc <- prettyM =<< asks elabEnvCtx
          return $
            "context:" //> ctxDoc $$
            "clause:" //> PP.pretty synClauseBody
    env <- ask
    env' <- checkDecls env wheres
    magnifyTC (const env') $ do
      debugBracket "checkClause" msg $ do
        clauseBody <- checkExpr synClauseBody clauseType
        return $ Clause pats clauseBody

checkPatterns
  :: (IsTerm t)
  => [SA.Pattern]
  -> Type t
  -- ^ Type of the clause that has the given 'SA.Pattern's in front.
  -> ([Pattern t] -> Type t -> CheckM t a)
  -- ^ Continuation taking the elaborated patterns, a list of terms
  -- corresponding to terms produced by the patterns, and the type of
  -- the body of the clause.
  -> CheckM t a
checkPatterns [] type_ cont = do
  cont [] type_
checkPatterns (synPat : synPats) type0 cont = do
  typeView <- whnfView type0
  case typeView of
    Pi dom cod0 ->
      checkPattern synPat dom cod0 $ \pat cod ->
      checkPatterns synPats cod $ \pats type_ ->
      cont (pat : pats) type_
    _ -> do
      checkError $ ExpectingPi type0

checkPattern
  :: (IsTerm t)
  => SA.Pattern
  -> Type t
  -- ^ Type of the matched thing.
  -> Type t
  -- ^ Type of what's past the matched thing.
  -> (Pattern t -> Term t -> CheckM t a)
  -- ^ The elaborated pattern, the term produced by the pattern.
  -> CheckM t a
checkPattern synPat patType type_ cont = case synPat of
  SA.VarP name -> do
    -- The type is already scoped over a single variable, so we're fine.
    extendEnv_ (name, patType) $ cont VarP type_
  SA.WildP _ -> do
    -- Same as above
    extendEnv_ ("_", patType) $ cont VarP type_
  SA.ConP dataCon synPats -> do
    -- Check that the 'dataCon' is a constructor for the 'patType' we
    -- have been given.
    sig <- askSignature
    let dataConDef = sigGetDefinition sig dataCon
        DataCon (Const tyCon) _ _ = ignoreContextual dataConDef
    case ignoreContextual (sigGetDefinition sig tyCon) of
      Constant _ Data{}   -> return ()
      Constant _ Record{} -> checkError $ PatternMatchOnRecord synPat tyCon
      _                   -> __IMPOSSIBLE__
    patTypeView <- whnfView patType
    case patTypeView of
      -- Here we don't care about the argument in 'Opened', because the
      -- match refers to whatever arguments the tyCon has in the type
      -- signature.
      App (Def tyCon') tyConArgs0 | tyCon == opndKey tyCon' -> do
        let Just tyConArgs = mapM isApply tyConArgs0
        -- Here we use the arguments of the 'tyCon' to open the
        -- definition of the 'dataCon'.
        let openDataCon = Opened dataCon $ opndArgs tyCon'
        DataCon _ _ dataConType <- openDefinition dataConDef (opndArgs tyCon')
        -- We unroll the type of the data constructor, and then we
        -- continue examining the patterns using the type of the data
        -- constructor chained to the rest of the type we were given.
        appliedDataConType <- openContextual dataConType tyConArgs
        (appliedDataConTypeTel, _) <- unrollPi appliedDataConType
        -- Here we form the term made up of the new variables we're
        -- bringing in scope by taking the type of the dataCon...
        t <- con openDataCon =<< mapM var (telVars appliedDataConTypeTel)
        -- ...which we then instantiate in the old type, taking care of
        -- weakening the rest.
        let numDataConArgs = telLength appliedDataConTypeTel
        rho <- subChain (subLift 1 (subWeaken numDataConArgs subId)) =<< subSingleton t
        type' <- telPi appliedDataConTypeTel =<< applySubst type_ rho
        debug "checkPattern" $ do
         typeDoc <- prettyM type_
         rhoDoc <- prettyM rho
         type'Doc <- prettyM type'
         return $
          "type:" //> typeDoc $$
          "rho:" //> rhoDoc $$
          "type':" //> type'Doc
        -- GO GO GO
        checkPatterns synPats type' $ \pats type'' -> do
          cont (ConP dataCon pats) type''
      _ -> do
        checkError $ ExpectingTyCon tyCon patType

-- Bringing everything together
------------------------------------------------------------------------

-- Checking programs
--------------------

checkProgram
  :: [SA.Decl]
  -> (forall t. (IsTerm t) => Signature t -> Maybe PP.Doc -> IO a) -> IO a
checkProgram decls ret = do
  tt <- confTermType <$> readConf
  case tt of
    "S"   -> checkProgram' (Proxy :: Proxy Simple) decls ret
    "GR"  -> checkProgram' (Proxy :: Proxy GraphReduce) decls ret
    -- "GRS" -> checkProgram' (Proxy :: Proxy GraphReduceSub) decls ret
    "GRU" -> checkProgram' (Proxy :: Proxy GraphReduceUnpack) decls ret
    "H"   -> checkProgram' (Proxy :: Proxy Hashed) decls ret
    type_ -> ret (sigEmpty :: Signature Simple) (Just ("Invalid term type" <+> PP.text type_))

checkProgram'
    :: forall t a. (IsTerm t)
    => Proxy t -> [SA.Decl] -> (Signature t -> Maybe PP.Doc -> IO a) -> IO a
checkProgram' _ decls0 ret = do
    quiet <- confQuiet <$> readConf
    unless quiet $ do
      drawLine
      putStrLn "-- Checking declarations"
    s <- initCheckState
    -- For the time being we always start a dummy block here
    (mbErr, sig, _) <- runTC sigEmpty () s $ do
      void $ checkDecls (initElabEnv C0) decls0
      checkSignature
    ret sig $ either Just (\() -> Nothing) mbErr
  where
    checkSignature :: TC t r (CheckState t) ()
    checkSignature = do
      sig <- askSignature
      unsolvedMvs <- metas sig
      quiet <- confQuiet <$> readConf
      unless quiet $ do
        mvNoSummary <- confNoMetasSummary <$> readConf
        mvReport <- confMetasReport <$> readConf
        mvOnlyUnsolved <- confMetasOnlyUnsolved <$> readConf
        when (not mvNoSummary || mvReport) $ do
          let solvedMvs = catMaybes $ map (sigLookupMetaBody sig) $ sigDefinedMetas sig
          drawLine
          putStrLn' $ "-- Solved Metas: " ++ show (length solvedMvs)
          putStrLn' $ "-- Unsolved Metas: " ++ show (HS.size unsolvedMvs)
          when mvReport $ do
            drawLine
            let mvsTypes = map (\mv -> (mv, sigGetMetaType sig mv)) $ sigDefinedMetas sig
            forM_ (sortBy (comparing fst) $ mvsTypes) $ \(mv, mvType) -> do
              let mbMvb = sigLookupMetaBody sig mv
              when (not (isJust mbMvb) || not mvOnlyUnsolved) $ do
                mvTypeDoc <- prettyM mvType
                putStrLn' $ render $
                  PP.pretty mv <+> PP.parens (PP.pretty (srcLoc mv)) <+> ":" //> mvTypeDoc
                when (not mvOnlyUnsolved) $ do
                  mvBody <- case mbMvb of
                    Nothing -> return "?"
                    Just mi -> prettyM mi
                  putStrLn' $ render $ PP.pretty mv <+> "=" <+> PP.nest 2 mvBody
                putStrLn' ""
        noProblemsSummary <- confNoProblemsSummary <$> readConf
        problemsReport <- confProblemsReport <$> readConf
        when (not noProblemsSummary || problemsReport) $  do
          drawLine
          ss <- use csSolveState
          putStrLn' . render =<< prettyM ss
        drawLine
      unless (HS.null unsolvedMvs) $ checkError $ UnsolvedMetas unsolvedMvs

    putStrLn' :: MonadIO m => String -> m ()
    putStrLn' = liftIO . putStrLn

    drawLine :: MonadIO m => m ()
    drawLine =
      putStrLn' "------------------------------------------------------------------------"

{-
-- Commands
------------------------------------------------------------------------

data Command
  = TypeOf SA.Expr
  | Normalize SA.Expr
  | ShowConstraints
  | ShowMeta Meta
  | Help
  deriving (Eq, Show)

parseCommand :: Signature t -> String -> Either PP.Doc Command
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
    scope = sigToScope ts

    parseAndScopeCheck = parseExpr >=> SA.scopeCheckExpr scope

    parseMeta s =
      case readMay s of
        Just mv ->
          Right MV{metaId = mv, metaSrcLoc = SA.noSrcLoc}
        _ ->
          Left $ "Invalid metavar id" <+> PP.text s

    runReadP :: ReadP.ReadP (String -> Either PP.Doc Command) -> Either PP.Doc Command
    runReadP p = case ReadP.readP_to_S p s0 of
      []            -> Left "Unrecognised command"
      ((f, s') : _) -> f s'

runCommand :: (IsTerm t) => Signature t -> Command -> IO (PP.Doc, Signature t)
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
      mbMvBody <- lookupMetaBody mv
      mvTypeDoc <- prettyM mvType
      mvBodyDoc <- case mbMvBody of
        Nothing -> return "?"
        Just mi -> prettyM mi
      return $
        PP.pretty mv <+> ":" <+> mvTypeDoc $$
        PP.pretty mv <+> "=" <+> mvBodyDoc
    Help -> do
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

inferExpr
  :: (IsTerm t)
  => Ctx t -> SA.Expr -> CheckM t (Term t, Type t)
inferExpr ctx synT = do
  type_ <- addMetaInCtx ctx set
  t <- checkExpr ctx synT type_
  return (t, type_)
-}
