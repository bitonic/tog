{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
module TypeCheck3
  ( -- * Program checking
    checkFile
  ) where

import qualified Control.Lens                     as L
import           Data.Proxy                       (Proxy(Proxy))
import qualified Data.HashSet                     as HS

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

type CheckM t = TC t (Env t) (CheckState t)
type CCheckM t = forall b. CheckM t b -> CheckM t b

-- Decls
------------------------------------------------------------------------

-- | Here we don't use continuations because we don't want the debugging
-- output to be nested across declarations.
checkDecl
  :: (IsTerm t)
  => Env t
  -> SA.Decl
  -> TC t r (CheckState t) (Env t)
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
        SA.Module_ module_  -> checkModule module_ cont
        SA.Import modu args -> checkImport modu args cont
        SA.Open modu        -> checkOpen modu cont

checkDecls :: (IsTerm t) => Env t -> [SA.Decl] -> TC t r (CheckState t) (Env t)
checkDecls env [] = do
  return env
checkDecls env (decl : decls) = do
  env' <- checkDecl env decl
  checkDecls env' decls

addConstantAndOpen
  :: (IsTerm t)
  => (QName -> Tel t -> Type t -> CheckM t ())
  -> QName
  -> Type t
  -> CCheckM t
addConstantAndOpen f name type_ cont = do
  tel <- asks envTel
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
    ctx <- asks envCtx
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
      ctx <- asks envCtx
      definitionallyEqual ctx set endType set
    addConstantAndOpen addData name type_ cont

checkRecord :: (IsTerm t) => SA.TypeSig -> CCheckM t
checkRecord (SA.Sig name absType) cont = do
    type_ <- checkExpr absType set
    -- Check that at the end of the type there is a 'Set'
    (tel, endType) <- unrollPi type_
    extendEnv (telToCtx tel) $ do
      ctx <- asks envCtx
      definitionallyEqual ctx set endType set
    -- We add it as a postulate first, because we don't know what the
    -- datacon is yet.
    addConstantAndOpen addPostulate name type_ cont

checkDataDef
    :: (IsTerm t)
    => QName
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
    -> CheckM t (QName, Natural, Type t)
    -- ^ Name of the datacon, number of arguments and type of the data
    -- constructor, scoped over the parameters of the data type.
checkDataCon appliedTyConType (SA.Sig dataCon synDataConType) = do
  atSrcLoc dataCon $ do
    dataConType <- checkExpr synDataConType set
    (vsTel, endType) <- unrollPi dataConType
    extendEnv (telToCtx vsTel) $ do
      appliedTyConType' <- weaken_ (telLength vsTel) appliedTyConType
      ctx <- asks envCtx
      definitionallyEqual ctx set appliedTyConType' endType
    return (dataCon, telLength vsTel, dataConType)

checkRecDef
    :: (IsTerm t)
    => QName
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Name of the parameters to the tycon.
    -> QName
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
        go (ctx :< (qNameName field, fieldType)) fields

addProjections
    :: forall t.
       (IsTerm t)
    => Opened QName t
    -- ^ Type constructor.
    -> Tel (Type t)
    -- ^ Arguments to the type constructors
    -> Var
    -- ^ Variable referring to the value of type record type itself,
    -- which is the last argument of each projection ("self").  Note
    -- that this variable will have all the context above in scope.
    -> [QName]
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
  :: (IsTerm t) => QName -> [SA.Clause] -> CCheckM t
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
          ctxDoc <- prettyM =<< asks envCtx
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

checkModule
  :: forall t. (IsTerm t) => SA.Module -> CCheckM t
checkModule (SA.Module moduleName pars0 exports decls) cont = do
  let msg =
        "name:" //> PP.pretty moduleName $$
        "pars:" //> PP.pretty pars0 $$
        "exports:" //> PP.pretty exports
  debugBracket_ "checkModule" msg $ do
    module_ <- go pars0 C0
    tel <- asks envTel
    addModule moduleName tel module_
    openDefinitionInEnv_ moduleName $ \_ -> cont
  where
    go :: SA.Params -> Ctx t -> CheckM t (Module t)
    go [] ctx = do
      extendEnv ctx $ startBlock $ do
        env <- ask
        void $ checkDecls env decls
      return $ Contextual (ctxToTel ctx) $ HS.fromList exports
    go ((n, synType) : pars) ctx = do
      type_ <- extendEnv ctx $ checkExpr synType set
      go pars $ ctx :< (n, type_)

checkImport
  :: (IsTerm t) => QName -> [SA.Expr] -> CCheckM t
checkImport moduleName0 synArgs0 cont = do
  (_, Module (Contextual tel0 names0)) <- getOpenedDefinition moduleName0

  let checkArgs T0 [] args = do
        openDefs (reverse args) (HS.toList names0)
      checkArgs ((_, type_) :> tel) (synArg : synArgs) args = do
        arg <- checkExpr synArg type_
        tel' <- instantiate_ tel arg
        checkArgs tel' synArgs (arg : args)
      checkArgs _ _ _ = do
        checkError $ MismatchingArgumentsForModule moduleName0 tel0 synArgs0

      openDefs _    []             = cont
      openDefs args (name : names) = openDefinitionInEnv name args $ \_ -> openDefs args names

  checkArgs tel0 synArgs0 []

checkOpen
  :: (IsTerm t) => QName -> CCheckM t
checkOpen _ cont = cont

-- Bringing everything together
------------------------------------------------------------------------

-- Checking programs
--------------------

checkFile
  :: SA.Module
  -> (forall t. (IsTerm t) => Signature t -> Maybe PP.Doc -> IO a) -> IO a
checkFile decls ret = do
  tt <- confTermType <$> readConf
  case tt of
    "S"   -> checkFile' (Proxy :: Proxy Simple) decls ret
    "GR"  -> checkFile' (Proxy :: Proxy GraphReduce) decls ret
    "GRU" -> checkFile' (Proxy :: Proxy GraphReduceUnpack) decls ret
    "H"   -> checkFile' (Proxy :: Proxy Hashed) decls ret
    type_ -> ret (sigEmpty :: Signature Simple) (Just ("Invalid term type" <+> PP.text type_))

checkFile'
    :: forall t a. (IsTerm t)
    => Proxy t -> SA.Module -> (Signature t -> Maybe PP.Doc -> IO a) -> IO a
checkFile' _ decls0 ret = do
    quiet <- confQuiet <$> readConf
    unless quiet $ do
      drawLine
      putStrLn "-- Checking declarations"
    s <- initCheckState
    -- For the time being we always start a dummy block here
    (mbErr, sig, _) <- runTC sigEmpty () s $ do
      magnifyTC (const (initEnv C0)) $ checkModule decls0 $ return ()
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
