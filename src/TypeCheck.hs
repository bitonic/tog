{-# LANGUAGE OverloadedStrings #-}
module TypeCheck
  ( TypeCheckConf(..)
  , defaultTypeCheckConf
  , availableTermTypes
  , checkProgram
  , TCState'
  , TCReport'
  ) where

import           Prelude                          hiding (abs, pi)

import           Control.Monad.Trans.Either       (EitherT(EitherT), runEitherT)
import           Control.Monad.Trans.Maybe        (MaybeT(MaybeT), runMaybeT)
import qualified Data.HashMap.Strict              as HMS
import qualified Data.HashSet                     as HS
import qualified Data.Map.Strict                  as Map
import           Data.Proxy                       (Proxy(Proxy))
import qualified Data.Set                         as Set

import           Prelude.Extended
import           Syntax.Internal                  (Name, MetaVar)
import qualified Syntax.Internal                  as A
import           Term
import           Term.Context                     (Ctx)
import qualified Term.Context                     as Ctx
import           Term.Impl
import qualified Term.Signature                   as Sig
import qualified Term.Telescope                   as Tel
import           PrettyPrint                      (($$), (<+>), (//>), render)
import qualified PrettyPrint                      as PP
import           TypeCheck.Monad

-- Configuration
------------------------------------------------------------------------

data TypeCheckConf = TypeCheckConf
  { tccTermType                :: String
  , tccQuiet                   :: Bool
  , tccNoMetaVarsSummary       :: Bool
  , tccMetaVarsReport          :: Bool
  , tccMetaVarsOnlyUnsolved    :: Bool
  , tccNoProblemsSummary       :: Bool
  , tccProblemsReport          :: Bool
  , tccDebug                   :: Bool
  , tccCheckMetaVarConsistency :: Bool
  , tccFastGetAbsName          :: Bool
  , tccDisableSynEquality      :: Bool
  }

defaultTypeCheckConf :: TypeCheckConf
defaultTypeCheckConf = TypeCheckConf "GR" True False False False False False False False False False

data TypeCheckState = TypeCheckState
  { tcsCheckMetaVarConsistency :: Bool
  , tcsFastGetAbsName          :: Bool
  , tcsDisableSynEquality      :: Bool
  }

-- Useful types
------------------------------------------------------------------------

type TC'      t a = TC      t (TypeCheckProblem t) TypeCheckState a
type StuckTC' t a = StuckTC t (TypeCheckProblem t) TypeCheckState a

type TCState'  t = TCState t (TypeCheckProblem t) TypeCheckState
type TCReport' t = TCReport t (TypeCheckProblem t)

-- Type checking
------------------------------------------------------------------------

-- Checking programs
--------------------

availableTermTypes :: [String]
availableTermTypes = ["GR", "S", "H", "SUSP"]

checkProgram
  :: TypeCheckConf -> [A.Decl]
  -> (forall t. (IsTerm t) => TCState' t -> IO a)
  -> IO (Either PP.Doc a)
checkProgram conf decls ret =
  case tccTermType conf of
    "S"  -> checkProgram' (Proxy :: Proxy Simple)      conf decls ret
    "GR" -> checkProgram' (Proxy :: Proxy GraphReduce) conf decls ret
    -- "EW" -> checkProgram' (Proxy :: Proxy EasyWeaken)  conf decls ret
    "H"  -> checkProgram' (Proxy :: Proxy Hashed)      conf decls ret
    -- "SUSP" -> checkProgram' (Proxy :: Proxy Suspension) conf decls ret
    type_ -> return $ Left $ "Invalid term type" <+> PP.text type_

checkProgram'
    :: forall t a. (IsTerm t)
    => Proxy t -> TypeCheckConf -> [A.Decl]
    -> (TCState' t -> IO a)
    -> IO (Either PP.Doc a)
checkProgram' _ conf decls0 ret = do
    unless (tccQuiet conf) $ do
      drawLine
      putStrLn "-- Checking declarations"
      drawLine
    let s = TypeCheckState (tccCheckMetaVarConsistency conf)
                           (tccFastGetAbsName conf)
                           (tccDisableSynEquality conf)
    errOrTs <- runEitherT (goDecls (initTCState s) decls0)
    case errOrTs of
      Left err -> return $ Left err
      Right t  -> Right <$> ret t
  where
    goDecls :: TCState' t -> [A.Decl] -> EitherT PP.Doc IO (TCState' t)
    goDecls ts [] = do
      lift $ unless (tccQuiet conf) $ report ts
      return ts
    goDecls ts (decl : decls) = do
      lift $ unless (tccQuiet conf) $ do
        putStrLn $ render decl
        let separate = case decl of
              A.TypeSig (A.Sig n _) -> case decls of
                A.FunDef n' _     : _  -> not $ n == n'
                A.DataDef n' _ _  : _  -> not $ n == n'
                A.RecDef n' _ _ _ : _  -> not $ n == n'
                []                     -> False
                _                      -> True
              _ ->
                not $ null decls
        when separate $ putStrLn ""
      let debug' = if (not (tccQuiet conf) && tccDebug conf) then enableDebug else id
      let describeProblem p =
            withSignatureTermM $ \sig -> prettyTypeCheckProblem sig p
      ((), ts') <- EitherT $ runTC typeCheckProblem describeProblem ts $ debug' $
        checkDecl decl >> solveProblems_
      goDecls ts' decls

    report :: TCState' t -> IO ()
    report ts = do
      let tr  = tcReport ts
      let sig = trSignature tr
      when (not (tccNoMetaVarsSummary conf) || tccMetaVarsReport conf) $ do
        let mvsTypes  = Sig.metaVarsTypes sig
        let mvsBodies = Sig.metaVarsBodies sig
        drawLine
        putStrLn $ "-- Solved MetaVars: " ++ show (HMS.size mvsBodies)
        putStrLn $ "-- Unsolved MetaVars: " ++ show (HMS.size mvsTypes - HMS.size mvsBodies)
        when (tccMetaVarsReport conf) $ do
          drawLine
          forM_ (sortBy (comparing fst) $ HMS.toList mvsTypes) $ \(mv, mvType) -> do
            let mbBody = HMS.lookup mv mvsBodies
            when (isNothing mbBody || not (tccMetaVarsOnlyUnsolved conf)) $ do
              mvTypeDoc <- prettyTerm sig mvType
              putStrLn $ render $
                PP.pretty mv <+> PP.parens (PP.pretty (A.mvSrcLoc mv)) <+> ":" //> mvTypeDoc
              when (not (tccMetaVarsOnlyUnsolved conf)) $ do
                mvBody <- case HMS.lookup mv mvsBodies of
                  Nothing      -> return "?"
                  Just mvBody0 -> prettyTerm sig mvBody0
                putStrLn $ render $ PP.pretty mv <+> "=" <+> PP.nest 2 mvBody
              putStrLn ""
      when (not (tccNoProblemsSummary conf) || tccProblemsReport conf) $ do
        drawLine
        putStrLn $ "-- Solved problems: " ++ show (HS.size (trSolvedProblems tr))
        putStrLn $ "-- Unsolved problems: " ++ show (Map.size (trUnsolvedProblems tr))
        when (tccProblemsReport conf) $ do
          drawLine
          -- We want to display problems bound to metavars first (the
          -- "roots").
          let compareStates ps1 ps2 = case (ps1, ps2) of
                (BoundToMetaVars _, BoundToMetaVars _) -> EQ
                (BoundToMetaVars _, BoundToProblem _)  -> LT
                (BoundToProblem _,  BoundToProblem _)  -> EQ
                (BoundToProblem _,  BoundToMetaVars _) -> GT
          let problems =
                sortBy (compareStates `on` problemState . snd) $ Map.toList $ trUnsolvedProblems tr
          forM_ problems $ \(pid, (Problem mbProb probState _ _)) -> do
            probDoc <- case mbProb of
              Nothing   -> return "Waiting to return."
              Just prob -> prettyTypeCheckProblem sig prob
            putStrLn $ render $
              PP.pretty pid $$
              PP.indent 2 (PP.pretty probState) $$
              PP.indent 2 probDoc
            putStrLn ""
      drawLine

    drawLine =
      putStrLn "------------------------------------------------------------------------"

checkDecl :: (IsTerm t) => A.Decl -> TC' t ()
checkDecl decl = do
  debugBracket_ ("*** checkDecl" $$ PP.pretty decl) $ atSrcLoc decl $ do
    case decl of
      A.TypeSig sig      -> checkTypeSig sig
      A.DataDef d xs cs  -> checkData d xs cs
      A.RecDef d xs c fs -> checkRec d xs c fs
      A.FunDef f clauses -> checkFunDef f clauses

checkTypeSig :: (IsTerm t) => A.TypeSig -> TC' t ()
checkTypeSig (A.Sig name absType) = do
    type_ <- isType Ctx.Empty absType
    addConstant name Postulate type_

checkData
    :: (IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Names of parameters to the tycon.
    -> [A.TypeSig]
    -- ^ Types for the data constructors.
    -> TC' t ()
checkData tyCon tyConPars dataCons = do
    tyConType <- definitionType =<< getDefinition tyCon
    addConstant tyCon (Data []) tyConType
    (tyConPars', endType) <- unrollPiWithNames tyConType tyConPars
    elimStuckTC (equalType tyConPars' endType set) $
      error $ "Type constructor does not return Set: " ++ show tyCon
    appliedTyConType <- ctxAppTC (def tyCon []) tyConPars'
    mapM_ (checkConstr tyCon tyConPars' appliedTyConType) dataCons

checkConstr
    :: (IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> Ctx (Type t)
    -- ^ Ctx with the parameters of the tycon.
    -> Type t
    -- ^ Tycon applied to the parameters.
    -> A.TypeSig
    -- ^ Data constructor.
    -> TC' t ()
checkConstr tyCon tyConPars appliedTyConType (A.Sig dataCon synDataConType) = do
  atSrcLoc dataCon $ do
    dataConType <- isType tyConPars synDataConType
    (vs, endType) <- unrollPi dataConType
    appliedTyConType' <- liftTermM $ Ctx.weaken_ vs appliedTyConType
    elimStuckTC (equalType (tyConPars Ctx.++ vs) appliedTyConType' endType) $ do
      checkError $ TermsNotEqual appliedTyConType' endType
    addDataCon dataCon tyCon (Tel.tel tyConPars) dataConType

checkRec
    :: (IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Name of the parameters to the tycon.
    -> Name
    -- ^ Name of the data constructor.
    -> [A.TypeSig]
    -- ^ Fields of the record.
    -> TC' t ()
checkRec tyCon tyConPars dataCon fields = do
    tyConType <- definitionType =<< getDefinition tyCon
    addConstant tyCon (Record dataCon []) tyConType
    (tyConPars', endType) <- unrollPiWithNames tyConType tyConPars
    void $ equalType tyConPars' endType set
    fieldsTel <- checkFields tyConPars' fields
    appliedTyConType <- ctxAppTC (def tyCon []) tyConPars'
    fieldsTel' <- liftTermM $ Tel.weaken_ 1 fieldsTel
    addProjections
      tyCon tyConPars' (boundVar "_") (map A.typeSigName fields)
      fieldsTel'
    let fieldsCtx = Tel.unTel fieldsTel
    appliedTyConType' <- liftTermM $ Ctx.weaken_ fieldsCtx appliedTyConType
    addDataCon dataCon tyCon (Tel.tel tyConPars') =<< ctxPiTC fieldsCtx appliedTyConType'

checkFields
    :: forall t. (IsTerm t)
    => Ctx t -> [A.TypeSig] -> TC' t (Tel.Tel (Type t))
checkFields ctx0 = go Ctx.Empty
  where
    go :: Ctx.Ctx (Type t) -> [A.TypeSig] -> TC' t (Tel.Tel (Type t))
    go ctx [] =
        return $ Tel.tel ctx
    go ctx (A.Sig field synFieldType : fields) = do
        fieldType <- isType (ctx0 Ctx.++ ctx) synFieldType
        extendContext ctx (field, fieldType) $ \ctx' -> do
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
    -> TC' t ()
addProjections tyCon tyConPars self fields0 =
    go $ zip fields0 $ map Field [0,1..]
  where
    go fields fieldTypes = case (fields, fieldTypes) of
      ([], Tel.Empty) ->
        return ()
      ((field, ix) : fields', Tel.Cons (_, fieldType) fieldTypes') -> do
        endType <- (`piTC` fieldType) =<< ctxAppTC (def tyCon []) tyConPars
        addProjection field ix tyCon (Tel.tel tyConPars) endType
        (go fields' <=< liftTermM . Tel.instantiate fieldTypes') =<< appTC (Var self) [Proj field ix]
      (_, _) -> error "impossible.addProjections: impossible: lengths do not match"

checkFunDef :: (IsTerm t) => Name -> [A.Clause] -> TC' t ()
checkFunDef fun synClauses = do
    funType <- definitionType =<< getDefinition fun
    clauses <- mapM (checkClause fun funType) synClauses
    inv <- checkInvertibility clauses
    addClauses fun inv

checkClause
  :: (IsTerm t)
  => Name -> Closed (Type t)
  -> A.Clause
  -> TC' t (Closed (Clause t))
checkClause fun funType (A.Clause synPats synClauseBody) = do
  (ctx, pats, _, clauseType) <- checkPatterns fun synPats funType
  let msg = do
        ctxDoc <- prettyContextTC ctx
        return $ "*** checkClause" $$
                 "context:" //> ctxDoc
  debugBracket msg $ do
    clauseBody <- check ctx synClauseBody clauseType
    -- This is an optimization: we want to remove as many MetaVars
    -- as possible so that we'll avoid recomputing things.
    -- TODO generalize this to everything which adds a term.
    clauseBody' <- withSignatureTermM $ \sig -> instantiateMetaVars sig clauseBody
    return $ Clause pats clauseBody'

checkPatterns
  :: (IsTerm t)
  => Name
  -> [A.Pattern]
  -> Type t
  -- ^ Type of the clause that has the given 'A.Pattern's in front.
  -> TC' t (Ctx (Type t), [Pattern], [Term t], Type t)
  -- ^ A context into the internal variables, list of internal patterns,
  -- a list of terms produced by their bindings, and the type of the
  -- clause body (scoped over the pattern variables).
checkPatterns _ [] type_ =
    return (Ctx.Empty, [], [], type_)
checkPatterns funName (synPat : synPats) type0 = atSrcLoc synPat $ do
  stuck <- matchPi_ type0 $ \dom cod -> fmap NotStuck $ do
    (ctx, pat, patVar) <- checkPattern funName synPat dom
    cod'  <- liftTermM $ Ctx.weaken 1 ctx cod
    cod'' <- liftTermM $ instantiate cod' patVar
    (ctx', pats, patsVars, bodyType) <- checkPatterns funName synPats cod''
    patVar' <- liftTermM $ Ctx.weaken_ ctx' patVar
    return (ctx Ctx.++ ctx', pat : pats, patVar' : patsVars, bodyType)
  checkPatternStuck funName stuck

checkPattern
    :: (IsTerm t)
    => Name
    -> A.Pattern
    -> Type t
    -- ^ Type of the matched thing.
    -> TC' t (Ctx (Type t), Pattern, Term t)
    -- ^ The context, the internal 'Pattern', and a 'Term' containing
    -- the term produced by it.
checkPattern funName synPat type_ = case synPat of
    A.VarP name -> do
      v <- varTC $ boundVar name
      return (Ctx.singleton name type_, VarP, v)
    A.WildP _ -> do
      v <- varTC $ boundVar "_"
      return (Ctx.singleton "_" type_, VarP, v)
    A.ConP dataCon synPats -> do
      DataCon typeCon tyConParsTel dataConType <- getDefinition dataCon
      typeConDef <- getDefinition typeCon
      case typeConDef of
        Constant (Data _)     _ -> return ()
        Constant (Record _ _) _ -> checkError $ PatternMatchOnRecord synPat typeCon
        _                       -> do doc <- prettyDefinitionTC typeConDef
                                      error $ "impossible.checkPattern " ++ render doc
      stuck <- matchTyCon typeCon type_ $ \typeConArgs -> fmap NotStuck $ do
        dataConTypeNoPars <- liftTermM $ Tel.substs tyConParsTel dataConType typeConArgs
        (ctx, pats, patsVars, _) <- checkPatterns funName synPats dataConTypeNoPars
        t <- conTC dataCon patsVars
        return (ctx ,ConP dataCon pats, t)
      checkPatternStuck funName stuck

-- TODO we can loosen this by postponing adding clauses.
checkPatternStuck :: (IsTerm t) => Name -> Stuck a -> TC' t a
checkPatternStuck funName stuck =
  case stuck of
    NotStuck x -> return x
    StuckOn _  -> checkError $ StuckTypeSignature funName

-- Checking
-----------

check
  :: (IsTerm t)
  => Ctx t -> A.Expr -> Type t -> TC' t (Term t)
check ctx synT type_ = atSrcLoc synT $ do
 let msg = do
       typeDoc <- prettyTermTC type_
       return $
         "*** check" $$
         "term:" //> PP.pretty synT $$
         "type:" //> typeDoc
 debugBracket msg $
   case synT of
     A.Con dataCon synArgs -> do
       DataCon tyCon tyConParsTel dataConType <- getDefinition dataCon
       metaVarIfStuck ctx type_ $ matchTyCon tyCon type_ $ \tyConArgs -> do
         appliedDataConType <- liftTermM $ Tel.substs tyConParsTel dataConType tyConArgs
         checkConArgs ctx synArgs appliedDataConType `bindStuckTC`
           WaitingOn (con dataCon)
     A.Refl _ -> do
       metaVarIfStuck ctx type_ $ matchEqual type_ $ \type' t1 t2 -> do
         checkEqual ctx type' t1 t2 `bindStuckTC` WaitingOn (\() -> return refl)
     A.Meta _ ->
       addMetaVarInCtx ctx type_
     A.Lam name synBody -> do
       metaVarIfStuck ctx type_ $ matchPi name type_ $ \dom cod -> do
         body <- extendContext ctx (name, dom) $ \ctx' -> check ctx' synBody cod
         returnStuckTC =<< lamTC body
     _ -> do
       metaVarIfStuck ctx type_ $
         infer ctx synT `bindStuckTC` CheckEqualInfer ctx type_

checkSpine
  :: (IsTerm t)
  => Ctx t -> Term t -> [A.Elim] -> Type t -> StuckTC' t (Term t, Type t)
checkSpine _ h [] type_ =
  returnStuckTC (h, type_)
checkSpine ctx h (el : els) type_ = atSrcLoc el $ case el of
  A.Proj proj -> do
    applyProjection proj h type_ `bindStuckTC` CheckSpine ctx els
  A.Apply synArg -> do
    matchPi_ type_ $ \dom cod -> do
      arg <- check ctx synArg dom
      cod' <- liftTermM $ instantiate cod arg
      h' <- eliminateTC h [Apply arg]
      checkSpine ctx h' els cod'

checkConArgs
  :: (IsTerm t)
  => Ctx t -> [A.Expr] -> Type t -> StuckTC' t [t]
checkConArgs _ [] _ = do
  returnStuckTC []
checkConArgs ctx (synArg : synArgs) type_ = atSrcLoc synArg $ do
  matchPi_ type_ $ \dom cod -> do
    arg <- check ctx synArg dom
    cod' <- liftTermM $ instantiate cod arg
    checkConArgs ctx synArgs cod' `bindStuckTC` WaitingOn (return . (arg :))

isType :: (IsTerm t) => Ctx t -> A.Expr -> TC' t (Type t)
isType ctx abs = check ctx abs set

-- Inference
------------

infer
  :: (IsTerm t)
  => Ctx t -> A.Expr -> StuckTC' t (Term t, Type t)
infer ctx synT = atSrcLoc synT $ do
  debugBracket_ ("*** infer" $$ PP.pretty synT) $
    case synT of
      A.Set _ ->
        returnStuckTC (set, set)
      A.Pi name synDomain synCodomain -> do
        domain   <- isType ctx synDomain
        codomain <- extendContext ctx (name, domain) $ \ctx' -> isType ctx' synCodomain
        t <- piTC domain codomain
        returnStuckTC (t, set)
      A.Fun synDomain synCodomain -> do
        infer ctx $ A.Pi "_" synDomain synCodomain
      A.App synH elims -> do
        (h, type_) <- inferHead ctx synH
        checkSpine ctx h elims type_
      A.Equal synType synX synY -> do
        type_ <- isType ctx synType
        x <- check ctx synX type_
        y <- check ctx synY type_
        t <- equalTC type_ x y
        returnStuckTC (t, set)
      _ -> do
        type_ <- addMetaVarInCtx ctx set
        t <- check ctx synT type_
        returnStuckTC (t, type_)

inferHead
  :: forall t. (IsTerm t)
  => Ctx t -> A.Head -> TC' t (Term t, Type t)
inferHead ctx synH = atSrcLoc synH $ case synH of
  A.Var name -> do
    mbV <- liftTermM $ Ctx.lookupName name ctx
    case mbV of
      Nothing -> do
        checkError $ NameNotInScope name
      Just (v, type_) -> do
        h <- appTC (Var v) []
        return (h, type_)
  A.TermVar i name -> do
    let v = V $ named name i
    type_ <- liftTermM $ Ctx.getVar v ctx
    h <- appTC (Var v) []
    return (h, type_)
  A.Def name -> do
    type_ <- definitionType =<< getDefinition name
    h <- appTC (Def name) []
    return (h, type_)
  A.J{} -> do
    h <- appTC J []
    return (h, typeOfJ)
  A.TermMeta mv -> do
    mvType <- getMetaVarType mv
    mbMvT <- getMetaVarBody mv
    h <- case mbMvT of
      Nothing -> appTC (Meta mv) []
      Just t  -> return t
    return (h, mvType)

-- Equality
------------

-- | INVARIANT: Either both terms have been typechecked against the
-- type, or is blocked.  Why would we ever get blocked types here?
-- Because sometimes we put placeholder metavariables for things that
-- have already been typechecked (see `checkEqualSpine').
checkEqual
  :: (IsTerm t)
  => Ctx t -> Type t -> Term t -> Term t -> StuckTC' t ()
checkEqual ctx type0 x0 y0 = do
  let msg = do
        typeDoc <- prettyTermTC type0
        xDoc <- prettyTermTC x0
        yDoc <- prettyTermTC y0
        return $
          "*** checkEqual" $$
          "type:" //> typeDoc $$
          "x:" //> xDoc $$
          "y:" //> yDoc
  debugBracket msg $ do
    blockedX0 <- whnfTC x0
    blockedY0 <- whnfTC y0
    x1 <- ignoreBlockingTC blockedX0
    y1 <- ignoreBlockingTC blockedY0
    -- Optimization: try with a simple syntactic check first.
    eq <- do
      disabled <- tcsDisableSynEquality <$> getState
      (not disabled &&) <$> liftTermM (blockedEq blockedX0 blockedY0)
    if eq
      then notStuck $ return ()
      else do
        postponeIfBlockedType (CheckEqual ctx type0 x1 y1) type0 $ \type1 -> do
          -- Eta-expansion
          (blockedX, blockedY) <- do
            debugBracket_ "*** Eta-expansion" $ do
              mbExpand <- etaExpand type1
              case mbExpand of
                Nothing -> do
                  return (blockedX0, blockedY0)
                Just expand -> do
                  x2 <- expand x1
                  y2 <- expand y1
                  let msg' = do
                        x2Doc <- prettyTermTC x2
                        y2Doc <- prettyTermTC y2
                        return $ "** Expanded to" $$ x2Doc $$ y2Doc
                  debug msg'
                  (,) <$> whnfTC x2 <*> whnfTC y2
          x2 <- ignoreBlockingTC blockedX
          y2 <- ignoreBlockingTC blockedY
          case (blockedX, blockedY) of
            (MetaVarHead mv els1, MetaVarHead mv' els2) | mv == mv' -> do
              mbKills <- intersectVars els1 els2
              case mbKills of
                Nothing -> do
                  checkSyntacticEquality (HS.singleton mv) type1 x2 y2
                Just kills -> do
                  instantiateMetaVar' mv =<< killArgs mv kills
                  notStuck $ return ()
            (MetaVarHead mv elims, _) ->
              metaAssign ctx type1 mv elims y2
            (_, MetaVarHead mv elims) ->
              metaAssign ctx type1 mv elims x2
            (BlockedOn mvs1 _ _, BlockedOn mvs2 _ _) -> do
              -- Both blocked, and we already checked for syntactic equality,
              -- let's try syntactic equality when normalized.
              x3 <- nfTC x2
              y3 <- nfTC y2
              eq' <- liftTermM $ termEq x3 y3
              if eq'
                then returnStuckTC ()
                else do
                  let mvs = HS.union mvs1 mvs2
                  debug_ $ "*** Both sides blocked, waiting for" <+> PP.pretty (HS.toList mvs)
                  stuckOn $ newProblem mvs $ CheckEqual ctx type1 x3 y3
            (BlockedOn mvs f elims, _) -> do
              checkEqualBlockedOn ctx type1 mvs f elims y2
            (_, BlockedOn mvs f elims) -> do
              checkEqualBlockedOn ctx type1 mvs f elims x2
            (NotBlocked _, NotBlocked _) -> do
               typeView <- viewTC type1
               xView <- viewTC x2
               yView <- viewTC y2
               let mkVar n ix = varTC $ V $ named n ix
               case (typeView, xView, yView) of
                 -- Note that here we rely on canonical terms to have canonical
                 -- types, and on the terms to be eta-expanded.
                 (Pi dom cod, Lam body1, Lam body2) -> do
                   -- TODO there is a bit of duplication between here and expansion.
                   name <- getAbsNameTC body1
                   extendContext ctx (name, dom) $ \ctx' -> checkEqual ctx' cod body1 body2
                 (Set, Pi dom1 cod1, Pi dom2 cod2) -> do
                   -- Pi : (A : Set) -> (A -> Set) -> Set
                   piType <- do
                     av <- mkVar "A" 0
                     b <- piTC av set
                     piTC set =<< piTC b set
                   cod1' <- lamTC cod1
                   cod2' <- lamTC cod2
                   checkEqualApplySpine ctx piType [dom1, cod1'] [dom2, cod2']
                 (Set, Equal type1' l1 r1, Equal type2' l2 r2) -> do
                   -- _==_ : (A : Set) -> A -> A -> Set
                   equalType_ <- do
                     xv <- mkVar "A" 0
                     yv <- mkVar "A" 1
                     piTC set =<< piTC xv =<< piTC yv set
                   checkEqualApplySpine ctx equalType_ [type1', l1, r1] [type2', l2, r2]
                 (Equal _ _ _, Refl, Refl) -> do
                   returnStuckTC ()
                 (App (Def _) tyConPars0, Con dataCon dataConArgs1, Con dataCon' dataConArgs2) | dataCon == dataCon' -> do
                    let Just tyConPars = mapM isApply tyConPars0
                    DataCon _ dataConTypeTel dataConType <- getDefinition dataCon
                    appliedDataConType <- liftTermM $ Tel.substs dataConTypeTel dataConType tyConPars
                    checkEqualApplySpine ctx appliedDataConType dataConArgs1 dataConArgs2
                 (Set, Set, Set) -> do
                   returnStuckTC ()
                 (_, App h1 elims1, App h2 elims2) | h1 == h2 -> do
                   equalSpine ctx h1 elims1 elims2
                 (_, _, _) -> do
                   checkError $ TermsNotEqual x1 y1
  where
    etaExpand type_ = do
      typeView <- viewTC type_
      case typeView of
        App (Def tyCon) _ -> do
          tyConDef <- getDefinition tyCon
          return $ case tyConDef of
            Constant (Record dataCon projs) _ ->
              Just $ \t -> do
                ts <- mapM (\(n, ix) -> eliminateTC t [Proj n ix]) projs
                conTC dataCon ts
            _ ->
              Nothing
        Pi _ codomain -> do
          name <- getAbsNameTC codomain
          v <- varTC $ boundVar name
          return $ Just $ \t -> do
            tView <- whnfViewTC t
            case tView of
              Lam _ -> return t
              _     -> do t' <- liftTermM $ weaken_ 1 t
                          lamTC =<< eliminateTC t' [Apply v]
        _ ->
          return Nothing

    checkSyntacticEquality mvs type_ x y = do
      x' <- nfTC x
      y' <- nfTC y
      eq' <- liftTermM $ termEq x' y'
      if eq'
        then notStuck $ return ()
        else do
          debug_ $ "*** Both sides blocked, waiting for" <+> PP.pretty (HS.toList mvs)
          stuckOn $ newProblem mvs $ CheckEqual ctx type_ x' y'


checkEqualApplySpine
  :: (IsTerm t)
  => Ctx t
  -> Type t
  -> [Term t]
  -> [Term t]
  -> StuckTC' t ()
checkEqualApplySpine ctx type_ args1 args2 =
  checkEqualSpine ctx type_ Nothing (map Apply args1) (map Apply args2)

checkEqualSpine
  :: (IsTerm t)
  => Ctx t
  -> Type t
  -- ^ Type of the head.
  -> Maybe (Term t)
  -- ^ Head, if we have it.
  -> [Elim (Term t)]
  -> [Elim (Term t)]
  -> StuckTC' t ()
checkEqualSpine _ _ _ [] [] =
  returnStuckTC ()
checkEqualSpine ctx type_ mbH (elim1 : elims1) (elim2 : elims2) = do
  let msg = do
        typeDoc <- prettyTermTC type_
        hDoc <- case mbH of
          Nothing -> return "No head"
          Just h  -> prettyTermTC h
        elims1Doc <- prettyElimsTC $ elim1 : elims1
        elims2Doc <- prettyElimsTC $ elim2 : elims2
        return $
          "*** checkEqualSpine" $$
          "type:" //> typeDoc $$
          "head:" //> hDoc $$
          "elims1:" //> elims1Doc $$
          "elims2:" //> elims2Doc
  debugBracket msg $ do
    let prob = CheckEqualSpine ctx type_ mbH (elim1 : elims1) (elim2 : elims2)
    postponeIfBlockedType prob type_ $ \type' -> do
      case (elim1, elim2) of
        (Apply arg1, Apply arg2) -> do
          typeView <- viewTC type'
          case typeView of
            Pi dom cod -> do
              stuck <- checkEqual ctx dom arg1 arg2
              let continue arg cod' = do
                    mbH' <- traverse (`eliminateTC` [Apply arg]) mbH
                    checkEqualSpine ctx cod' mbH' elims1 elims2
              case stuck of
                NotStuck () -> do
                  cod' <- liftTermM $ instantiate cod arg1
                  continue arg1 cod'
                -- If we're stuck in checking the domain, see if the
                -- function is dependent and if it's not continue checking
                -- and wait for both to complete.  otherwise put a
                -- metavariable as a placeholder for the argument and
                -- continue checking with that, forcing it to be equal to
                -- one of the arguments later.  Then wait for both problems
                -- to complete.
                StuckOn pid -> do
                  mbCod <- liftTermM $ strengthen_ 1 cod
                  case mbCod of
                    Just cod' -> do
                      debug_ "*** Stuck on domain but non-dependent."
                      stuck' <- continue arg1 cod'
                      case stuck' of
                        NotStuck () ->
                          stuckOn $ return pid
                        StuckOn pid' ->
                          stuckOn $ bindProblem pid $ WaitForProblem pid'
                    Nothing -> do
                      mvT <- addMetaVarInCtx ctx dom
                      debug $ do
                        mvTDoc <- prettyTermTC mvT
                        return $ "*** Stuck on domain, will use" <+> mvTDoc <+> "as type."
                      -- Check that the metavar is to the first arg once
                      -- we've proven that the two are equal...
                      pid1 <- bindProblem pid $ CheckEqual ctx dom mvT arg1
                      cod' <- liftTermM $ instantiate cod mvT
                      stuck' <- continue mvT cod'
                      case stuck' of
                        NotStuck () ->
                          -- TODO here we can instantiate immediately
                          stuckOn $ return pid1
                        StuckOn pid2 ->
                          stuckOn $ bindProblem pid1 $ WaitForProblem pid2
            _ -> do
              typeDoc <- prettyTermTC type'
              error $ "impossible.checkEqualSpine: Expected function type\n" ++ render typeDoc ++ "\n" ++ show type'
        (Proj proj projIx, Proj proj' projIx')
          | proj == proj' && projIx == projIx' ->
            case mbH of
              Nothing ->
                error $ "impossible.checkEqualSpine: got projection but no head."
              Just h  ->
                applyProjection proj h type_ `bindStuckTC`
                  CheckEqualSpine1 ctx elims1 elims2
        _ ->
          checkError $ SpineNotEqual type_ (elim1 : elims1) (elim1 : elims2)
checkEqualSpine _ type_ _ elims1 elims2 = do
  checkError $ SpineNotEqual type_ elims1 elims2

-- | @intersectVars us vs@ checks whether all relevant elements in @us@
--   and @vs@ are variables, and if yes, returns a prune list which says
--   @True@ for arguments which are different and can be pruned.
intersectVars :: (IsTerm t) => [Elim t] -> [Elim t] -> TC' t (Maybe [Named Bool])
intersectVars els1 els2 = runMaybeT $ mapM (uncurry areVars) $ zip els1 els2
  where
    areVars (Apply t1) (Apply t2) = do
      t1View <- lift $ viewTC t1
      t2View <- lift $ viewTC t2
      case (t1View, t2View) of
        (App (Var v1) [], App (Var v2) []) -> return $ (v1 /= v2) <$ unVar v1 -- prune different vars
        (_,               _)               -> mzero
    areVars _ _ =
      mzero

equalSpine
  :: (IsTerm t)
  => Ctx t -> Head -> [Elim t] -> [Elim t] -> StuckTC' t ()
equalSpine ctx h elims1 elims2 = do
  hType <- case h of
    Var v   -> liftTermM $ Ctx.getVar v ctx
    Def f   -> definitionType =<< getDefinition f
    J       -> return typeOfJ
    Meta mv -> getMetaVarType mv
  h' <- appTC h []
  checkEqualSpine ctx hType (Just h') elims1 elims2

postponeIfBlockedType
  :: (IsTerm t)
  => TypeCheckProblem t () () -> Type t -> (Type t -> StuckTC' t ())
  -> StuckTC' t ()
postponeIfBlockedType fallbackProb type_ ret = do
  blockedType <- whnfTC type_
  let fallback mvs = do
        debug $ do
          typeDoc <- prettyTermTC type_
          return $
             "*** postponeIfBlockedType" $$
             "Postponing:" //> typeDoc
        stuckOn $ newProblem mvs fallbackProb
  case blockedType of
    MetaVarHead mv _  -> fallback $ HS.singleton mv
    BlockedOn mvs _ _ -> fallback mvs
    NotBlocked type'  -> ret type'

checkEqualBlockedOn
  :: forall t.
     (IsTerm t)
  => Ctx t
  -> Type t
  -> HS.HashSet MetaVar
  -> BlockedHead -> [Elim t]
  -> Term t
  -> StuckTC' t ()
checkEqualBlockedOn ctx type_ mvs bh elims1 t2 = do
  let msg = "*** Equality blocked on metavars" <+> PP.pretty (HS.toList mvs) PP.<>
            ", trying to invert definition" <+> PP.pretty bh
  t1 <- ignoreBlockingTC $ BlockedOn mvs bh elims1
  debugBracket_ msg $ do
    case bh of
      BlockedOnJ -> do
        debug_ "** Head is J, couldn't invert."
        fallback t1
      BlockedOnFunction fun1 -> do
        Function _ clauses <- getDefinition fun1
        case clauses of
          NotInvertible _ -> do
            debug_ "** Couldn't invert."
            fallback t1
          Invertible injClauses -> do
            t2View <- whnfViewTC t2
            case t2View of
              App (Def fun2) elims2 | fun1 == fun2 -> do
                debug_ "** Could invert, and same heads, checking spines."
                equalSpine ctx (Def fun1) elims1 elims2
              _ -> do
                t2Head <- termHead =<< unviewTC t2View
                case t2Head of
                  Nothing -> do
                    debug_ "** Definition invertible but we don't have a clause head."
                    fallback t1
                  Just tHead | Just (Clause pats _) <- lookup tHead injClauses -> do
                    debug_ $ "Inverting on" <+> PP.pretty tHead
                    -- Make the eliminators match the patterns
                    matched <- matchPats pats elims1
                    -- And restart, if we matched something.
                    if matched
                      then checkEqual ctx type_ t1 t2
                      else fallback t1
                  Just _ -> do
                    checkError $ TermsNotEqual t1 t2
  where
    fallback t1 = stuckOn $ newProblem mvs $ CheckEqual ctx type_ t1 t2

    matchPats :: [Pattern] -> [Elim t] -> TC' t Bool
    matchPats (VarP : pats) (_ : elims) = do
      matchPats pats elims
    matchPats (ConP dataCon pats' : pats) (elim : elims) = do
      matched <- matchPat dataCon pats' elim
      (matched &&) <$> matchPats pats elims
    matchPats _ _ = do
      -- Less patterns than arguments is fine.
      --
      -- Less arguments than patterns is fine too -- it happens if we
      -- are waiting on some metavar which doesn't head an eliminator.
      return False

    matchPat :: Name -> [Pattern] -> Elim t -> TC' t Bool
    matchPat dataCon pats (Apply t) = do
      tView <- whnfViewTC t
      case tView of
        App (Meta mv) mvArgs -> do
          mvT <- instantiateDataCon mv dataCon
          void $ matchPat dataCon pats . Apply =<< eliminateTC mvT mvArgs
          return True
        Con dataCon' dataConArgs | dataCon == dataCon' ->
          matchPats pats (map Apply dataConArgs)
        _ -> do
          -- This can happen -- when we are blocked on metavariables
          -- that are impeding other definitions.
          return False
    matchPat _ _ _ = do
      -- Same as above.
      return False

equalType :: (IsTerm t) => Ctx t -> Type t -> Type t -> StuckTC' t ()
equalType ctx a b = checkEqual ctx set a b

-- Unification
------------------------------------------------------------------------

metaAssign
  :: (IsTerm t)
  => Ctx t -> Type t -> MetaVar -> [Elim (Term t)] -> Term t
  -> StuckTC' t ()
metaAssign ctx0 type0 mv elims0 t0 = do
  mvType <- getMetaVarType mv
  let msg = do
        mvTypeDoc <- prettyTermTC mvType
        elimsDoc <- prettyElimsTC elims0
        tDoc <- prettyTermTC t0
        return $
          "*** metaAssign" $$
          "assigning metavar:" <+> PP.pretty mv $$
          "of type:" //> mvTypeDoc $$
          "elims:" //> elimsDoc $$
          "to term:" //> tDoc
  debugBracket msg $ do
    -- Try to eta-expand the metavariable first.  If you can, eta-expand
    -- and restart the equality.  Otherwise, try to assign.
    (_, mvEndType) <- unrollPi mvType
    mbRecordDataCon <- runMaybeT $ do
      App (Def tyCon) _ <- lift $ whnfViewTC mvEndType
      Constant (Record dataCon _) _ <- lift $ getDefinition tyCon
      return dataCon
    case mbRecordDataCon of
      Just dataCon -> do
        let msg' = "*** Eta-expanding metavar " <+> PP.pretty mv <+>
                   "with datacon" <+> PP.pretty dataCon
        debugBracket_ msg' $ do
          mvT <- instantiateDataCon mv dataCon
          mvT' <- eliminateTC mvT elims0
          checkEqual ctx0 type0 mvT' t0
      Nothing -> do
        (ctx, elims, sub) <- etaExpandVars ctx0 elims0
        debug $ do
          -- TODO this check could be more precise
          if Ctx.length ctx0 == Ctx.length ctx
          then return "*** No change in context"
          else do
            ctxDoc <- prettyContextTC ctx
            return $ "*** New context:" //> ctxDoc
        type_ <- liftTermM $ sub type0
        t <- liftTermM $ sub t0
        debug $ do
          typeDoc <- prettyTermTC type_
          tDoc <- prettyTermTC t
          return $
            "** Type and term after eta-expanding vars:" $$
            "type:" //> typeDoc $$
            "term:" //> tDoc
        -- See if we can invert the metavariable
        ttInv <- invertMeta elims
        let invOrMvs = case ttInv of
              TTOK inv       -> Right inv
              TTMetaVars mvs -> Left $ HS.insert mv mvs
              -- TODO here we should also wait on metavars on the right that
              -- could simplify the problem.
              TTFail ()      -> Left $ HS.singleton mv
        case invOrMvs of
          Left mvs -> do
            debug_ $ "** Couldn't invert"
            -- If we can't invert, try to prune the variables not
            -- present on the right from the eliminators.
            t' <- nfTC t
            -- TODO should we really prune allowing all variables here?  Or
            -- only the rigid ones?
            fvs <- fvAll <$> freeVarsTC t'
            elims' <- mapM nf'TC elims
            mbMvT <- prune fvs mv elims'
            -- If we managed to prune them, restart the equality.
            -- Otherwise, wait on the metavariables.
            case mbMvT of
              Nothing -> do
                mvT <- metaVarTC mv elims
                stuckOn $ newProblem mvs $ CheckEqual ctx type_ mvT t
              Just mvT -> do
                mvT' <- eliminateTC mvT elims'
                checkEqual ctx type_ mvT' t'
          Right inv -> do
            t1 <- pruneTerm (Set.fromList $ invertMetaVars inv) t
            let msg' = do
                  t1Doc <- prettyTermTC t1
                  invDoc <- prettyInvertMetaTC inv
                  return $
                    "** Could invert" $$
                    "inversion:" //> invDoc $$
                    "pruned term:" //> t1Doc
            debug msg'
            t2 <- applyInvertMeta inv t1
            case t2 of
              TTOK t' -> do
                mvs <- metaVarsTC t'
                when (mv `HS.member` mvs) $
                  checkError $ OccursCheckFailed mv t'
                instantiateMetaVar' mv t'
                returnStuckTC ()
              TTMetaVars mvs -> do
                debug_ ("** Inversion blocked on" //> PP.pretty (HS.toList mvs))
                mvT <- metaVarTC mv elims
                stuckOn $ newProblem (HS.insert mv mvs) $ CheckEqual ctx type_ mvT t
              TTFail v ->
                checkError $ FreeVariableInEquatedTerm mv elims t v

-- | The term must be in normal form.
--
-- Returns the pruned term.
pruneTerm
    :: (IsTerm t)
    => Set.Set Var                -- ^ allowed vars
    -> Term t
    -> TC' t (Term t)
pruneTerm vs t = do
  tView <- whnfViewTC t
  case tView of
    Lam body -> do
      name <- getAbsNameTC body
      lamTC =<< pruneTerm (addVar name) body
    Pi domain codomain -> do
      name <- getAbsNameTC codomain
      join $ piTC <$> pruneTerm vs domain <*> pruneTerm (addVar name) codomain
    Equal type_ x y -> do
      join $ equalTC <$> pruneTerm vs type_ <*> pruneTerm vs x <*> pruneTerm vs y
    App (Meta mv) elims -> do
      mbMvT <- prune vs mv elims
      case mbMvT of
        Nothing  -> metaVarTC mv elims
        Just mvT -> eliminateTC mvT elims
    App h elims -> do
      appTC h =<< mapM pruneElim elims
    Set ->
      return set
    Refl ->
      return refl
    Con dataCon args ->
      conTC dataCon =<< mapM (pruneTerm vs) args
  where
    pruneElim (Apply t') = Apply <$> pruneTerm vs t'
    pruneElim (Proj n f) = return $ Proj n f

    addVar name = Set.insert (boundVar name) (Set.mapMonotonic (weakenVar_ 1) vs)

-- | Prunes a 'MetaVar' application and instantiates the new body.
-- Returns the the new body of the metavariable if we managed to prune
-- anything.
--
-- The term must be in normal form.
prune
    :: forall t.
       (IsTerm t)
    => Set.Set Var               -- ^ allowed vars
    -> MetaVar
    -> [Elim (Term t)]       -- ^ Arguments to the metavariable
    -> TC' t (Maybe (Closed (Term t)))
prune allowedVs oldMv elims | Just args <- mapM isApply elims = do
  mbKills <- sequence <$> mapM (shouldKill allowedVs) args
  case mbKills of
    Just kills0 | or kills0 -> do
      let msg = do
            elimsDoc <- prettyElimsTC elims
            return $
              "*** prune" $$
              "metavar:" <+> PP.pretty oldMv $$
              "elims:" //> elimsDoc $$
              "to kill:" //> PP.pretty kills0 $$
              "allowed vars:" //> PP.pretty (Set.toList allowedVs)
      debugBracket msg $ runMaybeT $ do
        oldMvType <- lift $ getMetaVarType oldMv
        (newMvTypeTel, newMvType, kills1) <- lift $ createNewMeta oldMvType kills0
        guard $ any unNamed kills1
        newMv <- lift $ addMetaVar =<< telPiTC newMvTypeTel newMvType
        mvT <- lift $ killArgs newMv kills1
        lift $ instantiateMetaVar' oldMv mvT
        return mvT
    _ -> do
      return Nothing
  where
    -- We build a telescope with only the non-killed types in.  This
    -- way, we can analyze the dependency between arguments and avoid
    -- killing things that later arguments depend on.
    --
    -- At the end of the telescope we put both the new metavariable and
    -- the remaining type, so that this dependency check will be
    -- performed on it as well.
    createNewMeta
      :: Type t -> [Bool] -> TC' t (Tel.Tel (Type t), Type t, [Named Bool])
    createNewMeta type_ [] =
      return (Tel.Empty, type_, [])
    createNewMeta type_ (kill : kills) = do
      typeView <- whnfViewTC type_
      case typeView of
        Pi domain codomain -> do
          name <- getAbsNameTC codomain
          (tel, endType, kills') <- createNewMeta codomain kills
          let notKilled = (Tel.Cons (name, domain) tel, endType, named name False : kills')
          if not kill
            then return notKilled
            else do
              mbTel <- liftTermM $ Tel.strengthen_ 1 tel
              mbEndType <- liftTermM $ strengthen_ 1 endType
              return $ case (mbTel, mbEndType) of
                (Just tel', Just endType') -> (tel', endType', named name True : kills')
                _                          -> notKilled
        _ ->
          error "impossible.createNewMeta: metavar type too short"
prune _ _ _ = do
  -- TODO we could probably do something more.
  return Nothing

killArgs :: (IsTerm t) => MetaVar -> [Named Bool] -> TC' t (Closed (Term t))
killArgs newMv kills = do
  let vs = reverse [ V (Named n ix)
                   | (ix, Named n kill) <- zip [0..] (reverse kills), not kill
                   ]
  body <- metaVarTC newMv . map Apply =<< mapM varTC vs
  foldl' (\body' _ -> lamTC =<< body') (return body) kills

-- | Returns whether the term should be killed, given a set of allowed
-- variables.
shouldKill
  :: (IsTerm t)
  => Set.Set Var -> Term t -> TC' t (Maybe Bool)
shouldKill vs t = runMaybeT $ do
  tView <- lift $ whnfViewTC t
  case tView of
    Lam _ ->
      mzero
    Con dataCon args -> do
      guard =<< lift (isRecordConstr dataCon)
      and <$> mapM (MaybeT . shouldKill vs) args
    App (Def f) _ -> do
      neutr <- lift $ withSignature $ \sig -> not (isNeutral sig f)
      if neutr then mzero else fallback
    _ ->
      fallback
  where
    fallback = lift $ withSignatureTermM $ \sig -> do
      fvs <- freeVars sig t
      return $ not (fvRigid fvs `Set.isSubsetOf` vs)

    -- | Check whether a term @Def f es@ could be reduced, if its arguments
    -- were different.
    isNeutral sig f =
      case Sig.getDefinition sig f of
        Constant{}    -> False
        DataCon{}     -> error $ "impossible.isNeutral: constructor " ++ show f
        Projection{}  -> error $ "impossible.isNeutral: projection " ++ show f
        Function{}    -> True
        -- TODO: more precise analysis
        -- We need to check whether a function is stuck on a variable
        -- (not meta variable), but the API does not help us...

-- | A substitution from variables of the term on the left of the
-- equation to terms inside the metavar.
--
-- We also store how many variables the metavar abstracts.
data InvertMeta t =
  InvertMeta [(Var, t)]
             -- This 'Var' refers to a variable in the term equated to
             -- the metavariable
             Int

invertMetaVars :: InvertMeta t -> [Var]
invertMetaVars (InvertMeta sub _) = map fst sub

prettyInvertMetaTC
  :: (IsTerm t) => InvertMeta t -> TC' t PP.Doc
prettyInvertMetaTC (InvertMeta ts vs) = do
  ts' <- forM ts $ \(v, t) -> do
    tDoc <- prettyTermTC t
    return $ PP.pretty (v, tDoc)
  return $ PP.list ts' $$ PP.pretty vs

-- | Tries to invert a metavariable given its parameters (eliminators),
-- providing a substitution for the term on the right if it suceeds.
-- Doing so amounts to check if the pattern condition is respected for
-- the arguments, although we employ various trick to get around it when
-- the terms are not variables.
--
-- 'TTMetaVars' if the pattern condition check is blocked on a some
-- 'MetaVar's.
--
-- 'TTFail' if the pattern condition fails.
invertMeta
  :: forall t.
     (IsTerm t)
  => [Elim (Term t)]
  -> TC' t (TermTraverse () (InvertMeta t))
invertMeta elims0 = case mapM isApply elims0 of
    -- First we build up a list of variables representing the bound
    -- arguments in the metavar body.
    Just args0 -> go args0 $ reverse [V (Named "_" ix) | (ix, _) <- zip [0..] args0]
    Nothing    -> return $ TTFail ()
  where
    -- Then we try to invert passing pairs of arguments to the
    -- metavariable and bound arguments of the body of the
    -- metavariable.
    go :: [Term t] -> [Var] -> TC' t (TermTraverse () (InvertMeta t))
    go args vs = do
      res <- checkArgs . zip args =<< mapM varTC vs
      return $ case res of
        TTFail ()      -> TTFail ()
        TTMetaVars mvs -> TTMetaVars mvs
        -- If we're good, we also check that each variable gets
        -- substituted with only one thing.
        TTOK sub       -> InvertMeta <$> checkLinearity sub <*> pure (length vs)

    -- The terms on the left are those outside the metavar body (its
    -- arguments), on the right the bound variables corrisponding to
    -- them.  We return an inversion from variables outside to terms
    -- inside.
    checkArgs :: [(Term t, Term t)] -> TC' t (TermTraverse () [(Var, Term t)])
    checkArgs xs = do
      res <- mapM (uncurry checkArg) xs
      return $ concat <$> sequenceA res

    checkArg
      :: Term t
      -- ^ Term outside (argument to the metavar)
      -> Term t
      -- ^ Term inside (corresponding bound variable)
      -> TC' t (TermTraverse () [(Var, Term t)])
    checkArg arg v = do
      blockedArg <- whnfTC arg
      case blockedArg of
        -- If the argument is a variable, we are simply going to replace
        -- it with the corresponding variable in the body of the meta.
        NotBlocked t -> do
          tView <- viewTC t
          case tView of
            App (Var v0) [] ->
              return $ pure [(v0, v)]
            -- If the argument is a record, we're going to substitute
            -- the variable on the right with projected terms inside the
            -- body of the metavariable.
            Con dataCon recArgs -> do
              DataCon tyCon _ _ <- getDefinition dataCon
              tyConDef <- getDefinition tyCon
              case tyConDef of
                Constant (Record _ fields) _ -> do
                  recArgs' <- forM (zip recArgs fields) $ \(recArg, (n, f)) ->
                    (recArg, ) <$> eliminateTC v [Proj n f]
                  checkArgs recArgs'
                _ ->
                  return $ TTFail ()
            _ ->
              return $ TTFail ()
        MetaVarHead mv _ ->
          return $ TTMetaVars $ HS.singleton mv
        BlockedOn mvs _ _ ->
          return $ TTMetaVars mvs

    checkLinearity :: [(Var, Term t)] -> TermTraverse () [(Var, Term t)]
    checkLinearity sub =
      traverse makeLinear $ groupBy ((==) `on` fst) $ sortBy (comparing fst) sub

    makeLinear :: [(Var, Term t)] -> TermTraverse () (Var, Term t)
    makeLinear []      = error "impossible.checkPatternCondition"
    makeLinear [x]     = pure x
    -- TODO Consider making this work for singleton types.
    makeLinear (_ : _) = TTFail ()

-- | Takes a meta inversion and applies it to a term.  Fails returning a
-- 'Var' if that 'Var' couldn't be substituted in the term.
applyInvertMeta
  :: forall t.
     (IsTerm t)
  => InvertMeta t -> Term t
  -> TC' t (TermTraverse Var (Closed (Term t)))
applyInvertMeta (InvertMeta sub vsNum) t = do
  tt <- applyInvertMetaSubst sub t
  case tt of
    TTFail v ->
      return $ TTFail v
    TTMetaVars mvs ->
      return $ TTMetaVars mvs
    TTOK t' -> do
      return . TTOK =<< lambdaAbstract vsNum t'

-- | Wraps the given term 'n' times.
lambdaAbstract :: (IsTerm t) => Int -> Term t -> TC' t (Term t)
lambdaAbstract n t | n <= 0 = return t
lambdaAbstract n t = (lamTC <=< lambdaAbstract (n - 1)) t

applyInvertMetaSubst
  :: forall t. (IsTerm t)
  => [(Var, Term t)]
  -- ^ Inversion from variables outside to terms inside
  -> Term t
  -- ^ Term outside
  -> TC' t (TermTraverse Var (Term t))
  -- ^ Either we fail with a variable that isn't present in the
  -- substitution, or we return a new term.
applyInvertMetaSubst sub t0 =
  flip go t0 $ \v -> return $ maybe (Left v) Right (lookup v sub)
  where
    lift' :: (Var -> TC' t (Either Var (Term t)))
          -> (Var -> TC' t (Either Var (Term t)))
    lift' f v0 = case strengthenVar_ 1 v0 of
      Nothing ->
        Right <$> varTC v0
      Just v -> do
        e <- f v
        case e of
          Left v' -> return $ Left v'
          Right t -> Right <$> (liftTermM (weaken_ 1 t))

    go :: (Var -> TC' t (Either Var (Term t))) -> Term t -> TC' t (TermTraverse Var t)
    go invert t = do
      tView <- whnfViewTC t
      case tView of
        Lam body -> do
          traverse lamTC =<< go (lift' invert) body
        Pi dom cod -> do
          dom' <- go invert dom
          cod' <- go (lift' invert) cod
          sequenceA $ piTC <$> dom' <*> cod'
        Equal type_ x y -> do
          type' <- go invert type_
          x' <- go invert x
          y' <- go invert y
          sequenceA $ equalTC <$> type' <*> x' <*> y'
        Refl ->
          return $ pure refl
        Con dataCon args -> do
          args' <- mapM (go invert) args
          sequenceA $ conTC dataCon <$> sequenceA args'
        Set ->
          return $ pure set
        App h elims -> do
          let goElim (Apply t') = fmap Apply <$> go invert t'
              goElim (Proj n f) = return $ pure $ Proj n f

          resElims <- sequenceA <$> mapM goElim elims
          case (h, resElims) of
            (Meta mv, TTMetaVars mvs) ->
              return $ TTMetaVars $ HS.insert mv mvs
            (Meta mv, TTFail _) ->
              return $ TTMetaVars $ HS.singleton mv
            (Var v, _) -> do
              inv <- invert v
              sequenceA $ eliminateTC <$> either TTFail pure inv <*> resElims
            (Def f, _) ->
              sequenceA $ appTC (Def f) <$> resElims
            (J, _) ->
              sequenceA $ appTC J <$> resElims
            (Meta mv, _) ->
              sequenceA $ appTC (Meta mv) <$> resElims

-- Eta-expansion of arguments of metas
--------------------------------------

-- | Eliminates projected variables by eta-expansion, thus modifying the
-- context.
etaExpandVars
  :: (IsTerm t)
  => Ctx t
  -- ^ Context we're in
  -> [Elim t]
  -- ^ Eliminators on the MetaVar
  -> TC' t (Ctx t, [Elim t], t -> TermM t)
  -- ^ Returns the new context, the new eliminators, and a substituting
  -- action to update terms to the new context.
etaExpandVars ctx0 elims0 = do
  elims1 <- mapM (etaContractElim <=< nf'TC) elims0
  let msg = do
        elimsDoc <- prettyElimsTC elims1
        return $
          "*** Eta-expand vars" $$
          "elims:" //> elimsDoc
  debugBracket msg $ do
    mbVar <- collectProjectedVar elims1
    case mbVar of
      Nothing ->
        return (ctx0, elims1, \t -> return t)
      Just (v, tyCon) -> do
        debug_ $ "** Found var" <+> PP.pretty v <+> "with tyCon" <+> PP.pretty tyCon
        let (ctx1, type_, tel) = splitContext ctx0 v
        (tel', sub) <- etaExpandVar tyCon type_ tel
        elims2 <- mapM (liftTermM . mapElimM sub) elims1
        (ctx2, elims3, sub') <- etaExpandVars (ctx1 Ctx.++ Tel.unTel tel') elims2
        return (ctx2, elims3, (sub >=> sub'))

-- | Expands a record-typed variable ranging over the given 'Tel.Tel',
-- returning a new telescope ranging over all the fields of the record
-- type and the old telescope with the variable substituted with a
-- constructed record, and a substitution for the old variable.
etaExpandVar
  :: (IsTerm t)
  => Name
  -- ^ The type constructor of the record type.
  -> Type t
  -- ^ The type of the variable we're expanding.
  -> Tel.Tel t
  -> TC' t (Tel.Tel t, t -> TermM t)
etaExpandVar tyCon type_ tel = do
  Constant (Record dataCon projs) _ <- getDefinition tyCon
  DataCon _ dataConTypeTel dataConType <- getDefinition dataCon
  App (Def _) tyConPars0 <- whnfViewTC type_
  let Just tyConPars = mapM isApply tyConPars0
  appliedDataConType <- liftTermM $ Tel.substs dataConTypeTel dataConType tyConPars
  (dataConPars, _) <- assert ("etaExpandVar, unrollPiWithNames:" <+>) $
    unrollPiWithNames appliedDataConType (map fst projs)
  dataConT <- conTC dataCon =<< mapM varTC (ctxVars dataConPars)
  tel' <- liftTermM $ Tel.subst 0 dataConT =<< Tel.weaken 1 1 tel
  let telLen = Tel.length tel'
  dataConT' <- liftTermM $ weaken_ telLen dataConT
  let sub t = subst telLen dataConT' =<< weaken (telLen + 1) 1 t
  return (dataConPars Tel.++ tel', sub)

-- | Scans a list of 'Elim's looking for an 'Elim' composed of projected
-- variable.
collectProjectedVar
  :: (IsTerm t) => [Elim t] -> TC' t (Maybe (Var, Name))
collectProjectedVar elims = runMaybeT $ do
  (v, projName) <- msum $ flip map elims $ \elim -> do
    Apply t <- return elim
    App (Var v) vElims <- lift $ whnfViewTC t
    projName : _ <- forM vElims $ \vElim -> do
      Proj projName _ <- return vElim
      return projName
    -- traceM "========"
    -- traceM $ show v
    -- vElimsDoc <- lift $ prettyElimsTC vElims
    -- traceM (PP.render vElimsDoc)
    return (v, projName)
  tyConDef <- lift $ getDefinition projName
  let Projection _ tyCon _ _ = tyConDef
  return (v, tyCon)

-- | Divides a context at the given variable.
splitContext
  :: Ctx t -> Var -> (Ctx t, Type t, Tel.Tel t)
splitContext ctx00 v0 = go ctx00 (varIndex v0) Tel.Empty
  where
    go ctx0 ix0 tel = case (ctx0, ix0) of
      (Ctx.Empty, _) ->
        error "impossible.splitContext: var out of scope"
      (Ctx.Snoc ctx (n', type_), ix) ->
        if ix > 0
        then go ctx (ix - 1) (Tel.Cons (n', type_) tel)
        else (ctx, type_, tel)

-- Eta-contraction of terms
---------------------------

etaContractElim :: (IsTerm t) => Elim t -> TC' t (Elim t)
etaContractElim (Apply t)  = Apply <$> etaContract t
etaContractElim (Proj n f) = return $ Proj n f

etaContract :: (IsTerm t) => t -> TC' t t
etaContract t0 = fmap (fromMaybe t0) $ runMaybeT $ do
  t0View <- lift $ whnfViewTC t0
  case t0View of
    -- TODO it should be possible to do it also for constructors
    Lam body -> do
      App h elims@(_:_) <- lift $ whnfViewTC =<< etaContract body
      Apply t <- return $ last elims
      App (Var v) [] <- lift $ whnfViewTC t
      guard $ varIndex v == 0
      Just t' <- lift $ liftTermM $ strengthen_ 1 =<< app h (init elims)
      return t'
    Con dataCon args -> do
      DataCon tyCon _ _ <- lift $ getDefinition dataCon
      Constant (Record _ fields) _ <- lift $ getDefinition tyCon
      guard $ length args == length fields
      (t : ts) <- sequence (zipWith isRightProjection fields args)
      guard =<< (and <$> lift (liftTermM (mapM (termEq t) ts)))
      return t
    _ ->
      mzero
  where
    isRightProjection (n, f) t = do
      App h elims@(_ : _) <- lift $ whnfViewTC =<< etaContract t
      Proj n' f' <- return $ last elims
      guard $ n == n' && f == f'
      lift $ nfTC =<< appTC h (init elims)

-- MetaVar handling
------------------------------------------------------------------------

addMetaVarInCtx
  :: (IsTerm t)
  => Ctx t -> Type t -> TC' t (Term t)
addMetaVarInCtx ctx type_ = do
  mv <- addMetaVar =<< ctxPiTC ctx type_
  ctxAppTC (metaVar mv []) ctx

createMvsPars
  :: (IsTerm t) => Ctx t -> Tel.Tel (Type t) -> TC' t [Term t]
createMvsPars _ Tel.Empty =
  return []
createMvsPars ctx (Tel.Cons (_, type') tel) = do
  mv  <- addMetaVarInCtx ctx type'
  mvs <- createMvsPars ctx =<< liftTermM (Tel.instantiate tel mv)
  return (mv : mvs)

-- Problem handling
------------------------------------------------------------------------

data TypeCheckProblem t a b where
  WaitingOn :: (a -> TermM b) -> TypeCheckProblem t a b
  WaitForProblem :: ProblemId a -> TypeCheckProblem t () a

  CheckEqual1      :: Ctx t -> Type t -> Term t
                   -> TypeCheckProblem t (Term t) ()
  CheckEqualInfer  :: Ctx t -> Type t
                   -> TypeCheckProblem t (Term t, Type t) (Term t)
  CheckSpine       :: Ctx t -> [A.Elim]
                   -> TypeCheckProblem t (Term t, Type t) (Term t, Type t)
  CheckEqual       :: Ctx t -> Type t -> Term t -> Term t
                   -> TypeCheckProblem t () ()
  CheckEqualSpine  :: Ctx t
                   -> Type t -> Maybe (Term t)
                   -> [Elim (Term t)] -> [Elim (Term t)]
                   -> TypeCheckProblem t () ()
  CheckEqualSpine1 :: Ctx t
                   -> [Elim (Term t)] -> [Elim (Term t)]
                   -> TypeCheckProblem t (Term t, Type t) ()

  MatchPi     :: Name -> Type t
              -> (Type t -> Abs (Type t) -> StuckTC' t a)
              -> TypeCheckProblem t () a
  MatchEqual  :: Type t
              -> (Type t -> Term t -> Term t -> StuckTC' t a)
              -> TypeCheckProblem t () a
  MatchTyCon  :: Name -> Type t
              -> ([Term t] -> StuckTC' t a)
              -> TypeCheckProblem t () a

typeCheckProblem
  :: (IsTerm t)
  => TypeCheckProblem t a b -> a -> StuckTC' t b
typeCheckProblem (WaitingOn f) x =
  returnStuckTC =<< liftTermM (f x)
typeCheckProblem (WaitForProblem pid) () =
  stuckOn $ bindProblem pid $ WaitingOn return
typeCheckProblem (CheckEqual1 ctx type_ t1) t2 =
  checkEqual ctx type_ t1 t2
typeCheckProblem (CheckEqualInfer ctx type_) (t, type') = do
  checkEqual ctx set type_ type' `bindStuckTC` WaitingOn (\() -> return t)
typeCheckProblem (CheckSpine ctx els) (h', type') = do
  checkSpine ctx h' els type'
typeCheckProblem (CheckEqual ctx type_ x y) () = do
  checkEqual ctx type_ x y
typeCheckProblem (CheckEqualSpine1 ctx elims1 elims2) (h', type') = do
  checkEqualSpine ctx type' (Just h') elims1 elims2
typeCheckProblem (CheckEqualSpine ctx type_ mbH elims1 elims2) () = do
  checkEqualSpine ctx type_ mbH elims1 elims2
typeCheckProblem (MatchPi n type_ handler) () =
  matchPi n type_ handler
typeCheckProblem (MatchEqual type_ handler) () =
  matchEqual type_ handler
typeCheckProblem (MatchTyCon n type_ handler) () =
  matchTyCon n type_ handler

prettyTypeCheckProblem
  :: (IsTerm t)
  => Sig.Signature t -> TypeCheckProblem t a b -> TermM PP.Doc
prettyTypeCheckProblem sig p = case p of
  WaitingOn _ -> do
    return "WaitingOn"
  WaitForProblem pid -> do
    return $ "WaitForProblem" <+> PP.pretty pid
  CheckEqual1 ctx type_ t1 -> do
    ctxDoc <- prettyContext sig ctx
    typeDoc <- prettyTerm sig type_
    t1Doc <- prettyTerm sig t1
    return $
      "CheckEqual1" $$
      "context:" //> ctxDoc $$
      "type:" <+> typeDoc $$
      "term:" <+> t1Doc
  CheckEqualInfer ctx type_ -> do
    ctxDoc <- prettyContext sig ctx
    typeDoc <- prettyTerm sig type_
    return $
      "CheckEqualInfer" $$
      "context:" //> ctxDoc $$
      "type:" <+> typeDoc
  CheckSpine ctx els -> do
    ctxDoc <- prettyContext sig ctx
    let elsDoc = PP.list $ map PP.pretty els
    return $
      "CheckSpine" $$
      "context:" //> ctxDoc $$
      "elims:" <+> elsDoc
  CheckEqual ctx type_ x y -> do
    ctxDoc <- prettyContext sig ctx
    typeDoc <- prettyTerm sig type_
    xDoc <- prettyTerm sig x
    yDoc <- prettyTerm sig y
    return $
      "CheckEqual" $$
      "context:" //> ctxDoc $$
      "type:" <+> typeDoc $$
      "x:" <+> xDoc $$
      "y:" <+> yDoc
  CheckEqualSpine1 ctx els1 els2 -> do
    ctxDoc <- prettyContext sig ctx
    els1Doc <- prettyElims sig els1
    els2Doc <- prettyElims sig els2
    return $
      "CheckEqualSpine1" $$
      "context:" //> ctxDoc $$
      "elims1:" <+> els1Doc $$
      "elims2:" <+> els2Doc
  CheckEqualSpine ctx type_ mbH els1 els2 -> do
    ctxDoc <- prettyContext sig ctx
    typeDoc <- prettyTerm sig type_
    hDoc <- case mbH of
      Nothing -> return "No head"
      Just h  -> prettyTerm sig h
    els1Doc <- prettyElims sig els1
    els2Doc <- prettyElims sig els2
    return $
      "CheckEqualSpine" $$
      "context:" //> ctxDoc $$
      "type:" <+> typeDoc $$
      "head:" <+> hDoc $$
      "elims1:" <+> els1Doc $$
      "elims2:" <+> els2Doc
  MatchPi _ type_ _ -> do
    typeDoc <- prettyTerm sig type_
    return $
      "MatchPi" $$
      "type:" <+> typeDoc
  MatchEqual type_ _ -> do
    typeDoc <- prettyTerm sig type_
    return $
      "MatchEqual" $$
      "type:" <+> typeDoc
  MatchTyCon n type_ _ -> do
    typeDoc <- prettyTerm sig type_
    return $
      "MatchTyCon" <+> PP.pretty n $$
      "type:" <+> typeDoc

metaVarIfStuck
  :: (IsTerm t)
  => Ctx t -> Type t -> StuckTC' t (Term t)
  -> TC' t (Term t)
metaVarIfStuck ctx type_ m = do
    stuck <- m
    case stuck of
      NotStuck t ->
        return t
      StuckOn pid -> do
        debug_ $ "*** metaVarIfStuck, adding MetaVar"
        mv <- addMetaVarInCtx ctx type_
        void $ bindProblem pid $ CheckEqual1 ctx type_ mv
        return mv

elimStuckTC :: StuckTC' t a -> TC' t a -> TC' t a
elimStuckTC m ifStuck = do
    stuck <- m
    case stuck of
      NotStuck x   -> return x
      StuckOn _pid -> ifStuck

-- -- Utils
-- ------------------------------------------------------------------------

-- -- Matching terms
-- -----------------

matchTyCon
  :: (IsTerm t)
  => Name
  -> Type t
  -> ([Term t] -> StuckTC' t a)
  -> StuckTC' t a
matchTyCon tyCon t0 handler = do
  blockedT <- whnfTC t0
  t <- ignoreBlockingTC blockedT
  let msg = do
        tDoc <- prettyTermTC t
        return $
          "*** matchTyCon" <+> PP.pretty tyCon $$
          "term:" //> tDoc
  debugBracket msg $ do
    mbRes <- runMaybeT $ case blockedT of
      NotBlocked _ -> do
        App (Def tyCon') tyConArgs0 <- lift $ whnfViewTC t
        guard (tyCon == tyCon')
        tyConArgs <- MaybeT $ return $ mapM isApply tyConArgs0
        lift $ handler tyConArgs
      MetaVarHead mv _ -> lift $ do
        mvType <- getMetaVarType mv
        (ctxMvArgs, _) <- unrollPi mvType
        Constant _ tyConType <- getDefinition tyCon
        (tyConParsCtx, _) <- unrollPi tyConType
        tyConPars <- createMvsPars ctxMvArgs $ Tel.tel tyConParsCtx
        mvT <- ctxLamTC ctxMvArgs =<< defTC tyCon (map Apply tyConPars)
        instantiateMetaVar' mv mvT
        -- TODO Dangerous recursion, relying on correct instantiation.
        -- Maybe remove and do it explicitly?
        matchTyCon tyCon t handler
      BlockedOn mvs _ _ -> lift $ do
        stuckOn $ newProblem mvs (MatchTyCon tyCon t handler)
    maybe (checkError $ DataConTypeError tyCon t) return mbRes

matchPi
  :: (IsTerm t)
  => Name                       -- ^ Name for the bound var in the codomain.
  -> Type t
  -> (Type t -> Abs (Type t) -> StuckTC' t a)
  -> StuckTC' t a
matchPi name t0 handler = do
  blockedT <- whnfTC t0
  t <- ignoreBlockingTC blockedT
  let msg = do
        tDoc <- prettyTermTC t
        return $ "*** matchPi" $$ tDoc
  debugBracket msg $ do
    mbRes <- runMaybeT $ case blockedT of
      NotBlocked _ -> do
        Pi dom cod <- lift $ whnfViewTC t
        lift $ handler dom cod
      MetaVarHead mv _ -> lift $ do
        mvType <- getMetaVarType mv
        (ctxMvArgs, _) <- unrollPi mvType
        dom <- addMetaVarInCtx ctxMvArgs set
        cod <- addMetaVarInCtx (Ctx.Snoc ctxMvArgs (name, dom)) set
        mvT <- ctxLamTC ctxMvArgs =<< piTC dom cod
        instantiateMetaVar' mv mvT
        -- TODO Dangerous recursion, relying on correct instantiation.
        -- Maybe remove and do it explicitly?
        matchPi name t handler
      BlockedOn mvs _ _ -> lift $ do
        stuckOn $ newProblem mvs (MatchPi name t handler)
    maybe (checkError $ ExpectedFunctionType t Nothing) return mbRes

matchPi_
  :: (IsTerm t)
  => Type t
  -> (Type t -> Abs (Type t) -> StuckTC' t a)
  -> StuckTC' t a
matchPi_ = matchPi "_"

matchEqual
  :: (IsTerm t)
  => Type t
  -> (Type t -> Term t -> Term t -> StuckTC' t a)
  -> StuckTC' t a
matchEqual t0 handler = do
  blockedT <- whnfTC t0
  t <- ignoreBlockingTC blockedT
  let msg = do
        tDoc <- prettyTermTC t
        return $ "*** matchEqual" $$ tDoc
  debugBracket msg $ do
    mbRes <- runMaybeT $ case blockedT of
      NotBlocked _ -> do
        Equal type_ t1 t2 <- lift $ whnfViewTC t
        lift $ handler type_ t1 t2
      MetaVarHead mv _ -> lift $ do
        mvType <- getMetaVarType mv
        (ctxMvArgs, _) <- unrollPi mvType
        type_ <- addMetaVarInCtx ctxMvArgs set
        t1 <- addMetaVarInCtx ctxMvArgs type_
        t2 <- addMetaVarInCtx ctxMvArgs type_
        mvT <- ctxLamTC ctxMvArgs =<< equalTC type_ t1 t2
        instantiateMetaVar' mv mvT
        matchEqual t handler
      BlockedOn mvs _ _ -> lift $ do
        stuckOn $ newProblem mvs (MatchEqual t handler)
    maybe (checkError $ ExpectedEqual t) return mbRes

applyProjection
  :: (IsTerm t)
  => Name
  -- ^ Name of the projection
  -> Term t
  -- ^ Head
  -> Type t
  -- ^ Type of the head
  -> StuckTC' t (Term t, Type t)
applyProjection proj h type_ = do
  Projection projIx tyCon projTypeTel projType <- getDefinition proj
  h' <- eliminateTC h [Proj proj projIx]
  matchTyCon tyCon type_ $ \tyConArgs -> do
    appliedProjType <- liftTermM $ Tel.substs projTypeTel projType tyConArgs
    appliedProjTypeView <- whnfViewTC appliedProjType
    case appliedProjTypeView of
      Pi _ endType -> do
        endType' <- liftTermM $ instantiate endType h
        returnStuckTC (h', endType')
      _ -> do
        doc <- prettyTermTC appliedProjType
        error $ "impossible.applyProjection: " ++ render doc

instantiateDataCon
  :: (IsTerm t)
  => MetaVar
  -> Name
  -- ^ Name of the datacon
  -> TC' t (Closed (Term t))
instantiateDataCon mv dataCon = do
  mvType <- getMetaVarType mv
  (ctxMvArgs, endType') <- unrollPi mvType
  DataCon tyCon dataConTypeTel dataConType <- getDefinition dataCon
  -- We know that the metavariable must have the right type (we have
  -- typechecked the arguments already).
  App (Def tyCon') tyConArgs0 <- whnfViewTC endType'
  Just tyConArgs <- return $ mapM isApply tyConArgs0
  True <- return $ tyCon == tyCon'
  appliedDataConType <- liftTermM $ Tel.substs dataConTypeTel dataConType tyConArgs
  (dataConArgsCtx, _) <- unrollPi appliedDataConType
  dataConArgs <- createMvsPars ctxMvArgs $ Tel.tel dataConArgsCtx
  mvT <- ctxLamTC ctxMvArgs =<< conTC dataCon dataConArgs
  instantiateMetaVar' mv mvT
  return mvT

-- Consistency checks
------------------------------------------------------------------------

instantiateMetaVar'
  :: (IsTerm t) => MetaVar -> Closed (Term t) -> TC' t ()
instantiateMetaVar' mv t = do
  checkConsistency <- tcsCheckMetaVarConsistency <$> getState
  if checkConsistency
    then do
      mvType <- getMetaVarType mv
      debugBracket_ ("*** Check metaVar" <+> PP.pretty mv) $ do
        solveProblems_
        absT <- liftTermM $ internalToTerm t
        _ <- assert ("impossible: inconsistent metavar body:" <+>) $ freeze $
             check Ctx.Empty absT mvType
        instantiateMetaVar mv t
    else do
      instantiateMetaVar mv t

-- Whnf'ing and view'ing
------------------------

nfTC :: (IsTerm t) => t -> TC' t t
nfTC t = withSignatureTermM $ \sig -> nf sig t

nf'TC :: (IsTerm t, Nf f) => f t -> TC' t (f t)
nf'TC t = withSignatureTermM $ \sig -> nf' sig t

whnfTC :: (IsTerm t) => t -> TC' t (Blocked t)
whnfTC t = withSignatureTermM $ \sig -> whnf sig t

whnfViewTC :: (IsTerm t) => t -> TC' t (TermView t)
whnfViewTC t = withSignatureTermM $ \sig -> whnfView sig t

viewTC :: (IsTerm t) => t -> TC' t (TermView t)
viewTC t = liftTermM $ view t

-- Unrolling Pis
----------------

-- TODO remove duplication

unrollPiWithNames
  :: (IsTerm t)
  => Type t
  -- ^ Type to unroll
  -> [Name]
  -- ^ Names to give to each parameter
  -> TC' t (Ctx (Type t), Type t)
  -- ^ A telescope with accumulated domains of the pis and the final
  -- codomain.
unrollPiWithNames type_ [] =
  return (Ctx.Empty, type_)
unrollPiWithNames type_ (name : names) = do
  typeView <- whnfViewTC type_
  case typeView of
    Pi domain codomain -> do
      (ctx, endType) <- unrollPiWithNames codomain names
      return (Ctx.singleton name domain Ctx.++ ctx, endType)
    _ -> do
      checkError $ ExpectedFunctionType type_ Nothing

unrollPi
  :: (IsTerm t)
  => Type t
  -- ^ Type to unroll
  -> TC' t (Ctx (Type t), Type t)
unrollPi type_ = do
  typeView <- whnfViewTC type_
  case typeView of
    Pi domain codomain -> do
      name <- getAbsNameTC codomain
      (ctx, endType) <- unrollPi codomain
      return (Ctx.singleton name domain Ctx.++ ctx, endType)
    _ ->
      return (Ctx.Empty, type_)

-- -- Errors
-- ---------

data CheckError t
    = DataConTypeError Name (Type t)
    | LambdaTypeError A.Expr (Type t)
    | NotEqualityType (Type t)
    | ExpectedFunctionType (Type t) (Maybe A.Expr)
    | CannotInferTypeOf A.Expr
    | TermsNotEqual (Term t) (Term t)
    | SpineNotEqual (Type t) [Elim t] [Elim t]
    | ExpectingRecordType (Type t)
    | FreeVariableInEquatedTerm MetaVar [Elim t] (Term t) Var
    | PatternMatchOnRecord A.Pattern
                           Name -- Record type constructor
    | MismatchingPattern (Type t) A.Pattern
    | OccursCheckFailed MetaVar (Closed (Term t))
    | ExpectedEqual (Term t)
    | WrongDeclInWhere A.Decl
    | NameNotInScope Name
    | StuckTypeSignature Name
    | ClausesAlreadyAdded Name

checkError :: (IsTerm t) => CheckError t -> TC' t a
checkError err = typeError =<< renderError err

renderError :: forall t. (IsTerm t) => CheckError t -> TC' t PP.Doc
renderError err = do
  case err of
    DataConTypeError synT type_ -> do
      typeDoc <- prettyTermTC type_
      return $ "DataCon type error" $$
               PP.nest 2 (PP.pretty synT $$ PP.nest 2 ":" $$ typeDoc)
    NotEqualityType type_ -> do
      typeDoc <- prettyTermTC type_
      return $ "Expecting an equality type:" $$ PP.nest 2 typeDoc
    LambdaTypeError synT type_ -> do
      typeDoc <- prettyTermTC type_
      return $ "Lambda type error:" $$
               PP.nest 2 (PP.pretty synT $$ PP.nest 2 ":" $$ typeDoc)
    ExpectedFunctionType type_ mbArg -> do
      typeDoc <- prettyTermTC type_
      return $ "Expected function type:" $$ PP.nest 2 typeDoc $$
               (case mbArg of
                  Nothing  -> ""
                  Just arg -> "In application of" $$ PP.nest 2 (PP.pretty arg))
    CannotInferTypeOf synT ->
      return $ "Cannot infer type of:" $$ PP.pretty synT
    TermsNotEqual t1 t2 -> do
      t1Doc <- prettyTermTC t1
      t2Doc <- prettyTermTC t2
      return $ t1Doc $$ PP.nest 2 "!=" $$ t2Doc
    SpineNotEqual type_ es1 es2 -> do
      typeDoc <- prettyTermTC type_
      es1Doc <- prettyElimsTC es1
      es2Doc <- prettyElimsTC es2
      return $ es1Doc $$ PP.nest 2 "!=" $$ es2Doc $$ PP.nest 2 ":" $$ typeDoc
    ExpectingRecordType type_ -> do
      typeDoc <- prettyTermTC type_
      return $ "Expecting record type:" $$ PP.nest 2 typeDoc
    FreeVariableInEquatedTerm mv els rhs v -> do
      mvDoc <- prettyTermTC =<< metaVarTC mv els
      rhsDoc <- prettyTermTC rhs
      return $ "Free variable `" PP.<> prettyVar v PP.<> "' in term equated to metavariable application:" $$
               mvDoc $$ PP.nest 2 "=" $$ rhsDoc
    PatternMatchOnRecord synPat tyCon -> do
      return $ "Cannot have pattern" <+> PP.pretty synPat <+> "for record type" <+> PP.pretty tyCon
    MismatchingPattern type_ synPat -> do
      typeDoc <- prettyTermTC type_
      return $ PP.pretty synPat <+> "does not match an element of type" $$ typeDoc
    OccursCheckFailed mv t -> do
      tDoc <- prettyTermTC t
      return $ "Attempt at recursive instantiation:" $$ PP.pretty mv <+> ":=" <+> tDoc
    ExpectedEqual type_ -> do
      typeDoc <- prettyTermTC type_
      return $ "Expected identity type:" $$ PP.nest 2 typeDoc
    NameNotInScope name -> do
      return $ "Name not in scope:" <+> PP.pretty name
    StuckTypeSignature name -> do
      return $ "Got stuck on the type signature when checking clauses for function `" PP.<> PP.pretty name PP.<> "'"
    ClausesAlreadyAdded fun -> do
      return $ "Clauses already added for function `" PP.<> PP.pretty fun PP.<> "'"
    WrongDeclInWhere decl -> do
      return $ "Unexpected declaration in where clause" $$ PP.pretty decl
  where
    prettyVar = PP.pretty . varName

-- Clauses invertibility
------------------------

termHead :: (IsTerm t) => t -> TC' t (Maybe TermHead)
termHead t = do
  tView <- whnfViewTC t
  case tView of
    App (Def f) _ -> do
      fDef <- getDefinition f
      return $ case fDef of
        Constant Data{}      _ -> Just $ DefHead f
        Constant Record{}    _ -> Just $ DefHead f
        -- TODO here we can't return 'Just' because we don't know if the
        -- postulate is going to be instantiated afterwards.  Ideally we'd
        -- have a "postulate" keyword to avoid this.
        Constant Postulate{} _ -> Nothing
        _                      -> Nothing
    Con f _ ->
      return $ Just $ DefHead f
    Pi _ _ ->
      return $ Just $ PiHead
    _ ->
      return $ Nothing

checkInvertibility
  :: (IsTerm t) => [Closed (Clause t)] -> TC' t (Closed (Invertible t))
checkInvertibility = go []
  where
    go injClauses [] =
      return $ Invertible $ reverse injClauses
    go injClauses (clause@(Clause _ body) : clauses) = do
      th <- termHead body
      case th of
        Just tHead | Nothing <- lookup tHead injClauses ->
          go ((tHead, clause) : injClauses) clauses
        _ ->
          return $ NotInvertible $ reverse (map snd injClauses) ++ (clause : clauses)

-- Telescope & context utils
----------------------------

-- telStrengthen :: (IsTerm f) => Tel.IdTel f (Suc v) -> TermM (Maybe (Tel.IdTel f v))
-- telStrengthen (Tel.Empty (Tel.Id t)) =
--   fmap (Tel.Empty . Tel.Id) <$> strengthen t
-- telStrengthen (Tel.Cons (n, t) tel0) = runMaybeT $ do
--   t' <- MaybeT $ strengthen t
--   tel' <- MaybeT $ telStrengthen tel0
--   return $ Tel.Cons (n, t') tel'

-- | Collects all the variables in the 'Ctx.Ctx'.
ctxVars :: forall t. (IsTerm t) => Ctx.Ctx (Type t) -> [Var]
ctxVars = reverse . go 0
  where
    go :: Int -> Ctx.Ctx (Type t) -> [Var]
    go _ Ctx.Empty                 = []
    go ix (Ctx.Snoc ctx (name, _)) = V (named name ix) : go (ix + 1) ctx

-- | Creates a 'Pi' type containing all the types in the 'Ctx' and
-- terminating with the provided 't'.
ctxPi :: IsTerm t => Ctx (Type t) -> Type t -> TermM (Type t)
ctxPi Ctx.Empty                  t = return t
ctxPi (Ctx.Snoc ctx (_n, type_)) t = ctxPi ctx =<< pi type_ t

-- | Creates a 'Lam' term with as many arguments there are in the
-- 'Ctx.Ctx'.
ctxLam :: IsTerm t => Ctx (Type t) -> Term t -> TermM (Term t)
ctxLam Ctx.Empty        t = return t
ctxLam (Ctx.Snoc ctx _) t = ctxLam ctx =<< lam t

extendContext
  :: (IsTerm t)
  => Ctx (Type t) -> (Name, Type t) -> (Ctx (Type t) -> TC' t a) -> TC' t a
extendContext ctx type_ ret = do
  let ctx' = Ctx.Snoc ctx type_
  let msg = do
        ctxDoc <- prettyContextTC ctx'
        return $ "*** extendContext" $$ ctxDoc
  debugBracket msg $ ret ctx'

-- Monad versions of signature-requiring things
-----------------------------------------------

ctxAppTC :: (IsTerm t) => TermM (Term t) -> Ctx (Type t) -> TC' t (Term t)
ctxAppTC t ctx0 = do
  t' <- liftTermM t
  eliminateTC t' . map Apply =<< mapM varTC (ctxVars ctx0)

eliminateTC :: (IsTerm t) => t -> [Elim t] -> TC' t t
eliminateTC h els = withSignatureTermM $ \sig -> eliminate sig h els

freeVarsTC :: (IsTerm t) => t -> TC' t FreeVars
freeVarsTC t = withSignatureTermM $ \sig -> freeVars sig t

metaVarsTC :: (IsTerm t) => t -> TC' t (HS.HashSet MetaVar)
metaVarsTC t = withSignatureTermM $ \sig -> metaVars sig t

prettyTermTC :: (IsTerm t) => t -> TC' t PP.Doc
prettyTermTC t = withSignatureTermM $ \sig -> prettyTerm sig t

prettyElimTC :: (IsTerm t) => Elim t -> TC' t PP.Doc
prettyElimTC t = withSignatureTermM $ \sig -> prettyElim sig t

prettyElimsTC :: (IsTerm t) => [Elim t] -> TC' t PP.Doc
prettyElimsTC es = withSignatureTermM $ \sig -> prettyElims sig es

prettyDefinitionTC :: (IsTerm t) => Closed (Definition t) -> TC' t PP.Doc
prettyDefinitionTC def' = withSignatureTermM $ \sig -> prettyDefinition sig def'

prettyContextTC :: (IsTerm t) => Ctx.Ctx t -> TC' t PP.Doc
prettyContextTC ctx = withSignatureTermM $ \sig -> prettyContext sig ctx

unviewTC :: (IsTerm t) => TermView t -> TC' t t
unviewTC = liftTermM . unview

lamTC :: (IsTerm t) => Abs t -> TC' t t
lamTC body = liftTermM $ unview $ Lam body

piTC :: (IsTerm t) => t -> Abs t -> TC' t  t
piTC domain codomain = liftTermM $ unview $ Pi domain codomain

equalTC :: (IsTerm t) => t -> t -> t -> TC' t t
equalTC type_ x y = liftTermM $ unview $ Equal type_ x y

appTC :: (IsTerm t) => Head -> [Elim t] -> TC' t t
appTC h elims = liftTermM $ unview $ App h elims

metaVarTC :: (IsTerm t) => MetaVar -> [Elim t] -> TC' t t
metaVarTC mv = liftTermM . unview . App (Meta mv)

defTC :: (IsTerm t) => Name -> [Elim t] -> TC' t t
defTC f = liftTermM . unview . App (Def f)

conTC :: (IsTerm t) => Name -> [t] -> TC' t t
conTC c args = liftTermM $ unview (Con c args)

varTC :: (IsTerm t) => Var -> TC' t t
varTC = liftTermM . var

ctxLamTC :: (IsTerm t) => Ctx.Ctx (Type t) -> Term t -> TC' t (Term t)
ctxLamTC ctx = liftTermM . ctxLam ctx

ctxPiTC :: (IsTerm t) => Ctx (Type t) -> Type t -> TC' t (Type t)
ctxPiTC ctx type_ = liftTermM $ ctxPi ctx type_

telPiTC :: (IsTerm t) => Tel.Tel (Type t) -> Type t -> TC' t (Type t)
telPiTC tel = ctxPiTC (Tel.unTel tel)

ignoreBlockingTC :: (IsTerm t) => Blocked t -> TC' t t
ignoreBlockingTC = liftTermM . ignoreBlocking

-- Miscellanea
--------------

isApply :: Elim (Term t) -> Maybe (Term t)
isApply (Apply v) = Just v
isApply Proj{}    = Nothing

definitionType :: (IsTerm t) => Closed (Definition t) -> TC' t (Closed (Type t))
definitionType (Constant _ type_)         = return type_
definitionType (DataCon _ tel type_)      = telPiTC tel type_
definitionType (Projection _ _ tel type_) = telPiTC tel type_
definitionType (Function type_ _)         = return type_

isRecordType :: (IsTerm t) => Name -> TC' t Bool
isRecordType tyCon = withSignature $ \sig ->
  case Sig.getDefinition sig tyCon of
    Constant (Record _ _) _ -> True
    _                       -> False

isRecordConstr :: (IsTerm t) => Name -> TC' t Bool
isRecordConstr dataCon = join $ withSignature $ \sig ->
  case Sig.getDefinition sig dataCon of
    DataCon tyCon _ _ -> isRecordType tyCon
    _                 -> return False

getAbsNameTC
  :: (IsTerm t) => Abs (Term t) -> TC' t Name
getAbsNameTC t = do
  fast <- tcsFastGetAbsName <$> getState
  if fast
    then return "_"
    else liftTermM $ getAbsName_ t
