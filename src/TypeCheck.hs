{-# LANGUAGE OverloadedStrings #-}
module TypeCheck (TypeCheckConf(..), checkProgram, TCState') where

import           Prelude                          hiding (abs, pi)

import           Bound                            (Var(F, B))
import           Control.Applicative              (Applicative(pure, (<*>)))
import           Control.Monad                    (when, void, guard, mzero, forM, msum, join, (<=<), unless)
import           Control.Monad.Trans              (lift)
import           Control.Monad.Trans.Either       (EitherT(EitherT), runEitherT)
import           Control.Monad.Trans.Maybe        (MaybeT(MaybeT), runMaybeT)
import           Data.Foldable                    (forM_)
import           Data.Function                    (on)
import           Data.Functor                     ((<$>), (<$))
import qualified Data.HashMap.Strict              as HMS
import qualified Data.HashSet                     as HS
import           Data.List                        (sortBy, groupBy)
import           Data.Maybe                       (fromMaybe, isJust)
import           Data.Ord                         (comparing)
import           Data.Proxy                       (Proxy(Proxy))
import qualified Data.Set                         as Set
import           Data.Traversable                 (traverse, sequenceA)
import           Data.Typeable                    (Typeable)
import           Data.Void                        (absurd)

import           Syntax.Internal                  (Name)
import qualified Syntax.Internal                  as A
import           Term
import qualified Term.Context                     as Ctx
import qualified Term.Context.Utils               as Ctx
import           Term.Impl
import qualified Term.Signature                   as Sig
import qualified Term.Telescope                   as Tel
import           Text.PrettyPrint.Extended        (($$), (<>), (<+>), render)
import qualified Text.PrettyPrint.Extended        as PP
import           TypeCheck.Monad

-- Configuration
------------------------------------------------------------------------

data TypeCheckConf = TypeCheckConf
  { tccTermType             :: String
  , tccMetaVarsSummary      :: Bool
  , tccMetaVarsReport       :: Bool
  , tccMetaVarsOnlyUnsolved :: Bool
  , tccProblemsSummary      :: Bool
  , tccProblemsReport       :: Bool
  }

-- Useful types
------------------------------------------------------------------------

type Ctx t v = Ctx.ClosedCtx t v

type TC'      t a = TC      t (TypeCheckProblem t) a
type StuckTC' t a = StuckTC t (TypeCheckProblem t) a

type TCState' t = TCState t (TypeCheckProblem t)

-- Type checking
------------------------------------------------------------------------

-- Checking programs
--------------------

checkProgram
  :: TypeCheckConf -> [A.Decl]
  -> (forall t. (IsTerm t) => TCState' t -> IO a)
  -> IO (Either PP.Doc a)
checkProgram conf decls ret =
  case tccTermType conf of
    "S"  -> checkProgram' (Proxy :: Proxy Simple)      conf decls ret
    "GR" -> checkProgram' (Proxy :: Proxy GraphReduce) conf decls ret
    type_ -> return $ Left $ "Invalid term type" <+> PP.text type_

checkProgram'
    :: forall t a. (IsTerm t)
    => Proxy t -> TypeCheckConf -> [A.Decl]
    -> (TCState' t -> IO a)
    -> IO (Either PP.Doc a)
checkProgram' _ conf decls0 ret = do
    drawLine
    putStrLn "-- Checking declarations"
    drawLine
    errOrTs <- runEitherT (goDecls initTCState decls0)
    case errOrTs of
      Left err -> return $ Left err
      Right t  -> Right <$> ret t
  where
    goDecls :: TCState' t -> [A.Decl] -> EitherT PP.Doc IO (TCState' t)
    goDecls ts [] = do
      lift $ report ts
      return ts
    goDecls ts (decl : decls) = do
      lift $ putStrLn $ render decl
      ((), ts') <- EitherT $ runTC typeCheckProblem ts $ checkDecl decl >> solveProblems_
      goDecls ts' decls

    report :: TCState' t -> IO ()
    report ts = do
      let tr  = tcReport ts
      let sig = trSignature tr
      when (tccMetaVarsSummary conf || tccMetaVarsReport conf) $ do
        let mvsTypes  = Sig.metaVarsTypes sig
        let mvsBodies = Sig.metaVarsBodies sig
        drawLine
        putStrLn $ "-- Solved MetaVars: " ++ show (HMS.size mvsBodies)
        putStrLn $ "-- Unsolved MetaVars: " ++ show (HMS.size mvsTypes - HMS.size mvsBodies)
        when (tccMetaVarsReport conf) $ do
          drawLine
          forM_ (sortBy (comparing fst) $ HMS.toList mvsTypes) $ \(mv, mvType) -> do
            mvTypeDoc <- prettyTerm sig mvType
            putStrLn $ render $ PP.pretty mv <+> ":" <+> PP.nest 2 mvTypeDoc
            let mbBody = HMS.lookup mv mvsBodies
            unless (tccMetaVarsOnlyUnsolved conf || isJust mbBody) $ do
              mvBody <- case HMS.lookup mv mvsBodies of
                Nothing      -> return "?"
                Just mvBody0 -> prettyTerm sig mvBody0
              putStrLn $ render $ PP.pretty mv <+> "=" <+> PP.nest 2 mvBody
              putStrLn ""
      when (tccProblemsSummary conf || tccProblemsReport conf) $ do
        drawLine
        putStrLn $ "-- Solved problems: " ++ show (HS.size (trSolvedProblems tr))
        putStrLn $ "-- Unsolved problems: " ++ show (HMS.size (trUnsolvedProblems tr))
        -- when (tccProblemsReport conf) $ do
        --   drawLine
        --   forM_ (HMS.toList (trUnsolvedProblems tr)) $ \(pid, prob) -> do
        --     let desc = render $
        --           PP.pretty pid $$
        --           PP.nest 2 (PP.pretty probState) $$
        --           PP.nest 2 probDesc
        --     putStrLn desc
        --     putStrLn ""
      drawLine

    drawLine =
      putStrLn "------------------------------------------------------------------------"

checkDecl :: (IsTerm t) => A.Decl -> TC' t ()
checkDecl decl = atSrcLoc decl $ do
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
    unrollPiWithNames tyConType tyConPars $ \tyConPars' endType -> do
        elimStuckTC (equalType tyConPars' endType set) $
          error $ "Type constructor does not return Set: " ++ show tyCon
        appliedTyConType <- ctxAppTC (def tyCon []) tyConPars'
        mapM_ (checkConstr tyCon tyConPars' appliedTyConType) dataCons

checkConstr
    :: (IsVar v, IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> Ctx.ClosedCtx (Type t) v
    -- ^ Ctx with the parameters of the tycon.
    -> Type t v
    -- ^ Tycon applied to the parameters.
    -> A.TypeSig
    -- ^ Data constructor.
    -> TC' t ()
checkConstr tyCon tyConPars appliedTyConType (A.Sig dataCon synDataConType) = do
  atSrcLoc dataCon $ do
    dataConType <- isType tyConPars synDataConType
    unrollPi dataConType $ \vs endType -> do
      appliedTyConType' <- liftTermM $ Ctx.weaken vs appliedTyConType
      elimStuckTC (equalType (tyConPars Ctx.++ vs) appliedTyConType' endType) $ do
        checkError $ TermsNotEqual appliedTyConType' endType
    addDataCon dataCon tyCon (Tel.idTel tyConPars dataConType)

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
    unrollPiWithNames tyConType tyConPars $ \tyConPars' endType -> do
        void $ equalType tyConPars' endType set
        fieldsTel <- checkFields tyConPars' fields
        appliedTyConType <- ctxAppTC (def tyCon []) tyConPars'
        fieldsTel' <- liftTermM $ subst'Map F fieldsTel
        addProjections
          tyCon tyConPars' (boundTermVar "_") (map A.typeSigName fields)
          fieldsTel'
        Tel.unTel fieldsTel $ \fieldsCtx Tel.Proxy -> do
          appliedTyConType' <- liftTermM $ Ctx.weaken fieldsCtx appliedTyConType
          addDataCon dataCon tyCon . Tel.idTel tyConPars' =<< ctxPiTC fieldsCtx appliedTyConType'

checkFields
    :: forall v t. (IsVar v, IsTerm t)
    => Ctx t v -> [A.TypeSig] -> TC' t (Tel.ProxyTel (Type t) v)
checkFields ctx0 = go Ctx.Empty
  where
    go :: forall v' . (IsVar v')
       => Ctx.Ctx v (Type t) v' -> [A.TypeSig] -> TC' t (Tel.ProxyTel (Type t) v)
    go ctx [] =
        return $ Tel.proxyTel ctx
    go ctx (A.Sig field synFieldType : fields) = do
        fieldType <- isType (ctx0 Ctx.++ ctx) synFieldType
        go (Ctx.Snoc ctx (field, fieldType)) fields

addProjections
    :: (IsVar v, IsTerm t)
    => Name
    -- ^ Type constructor.
    -> Ctx (Type t) v
    -- ^ A context with the parameters to the type constructor.
    -> TermVar v
    -- ^ Variable referring to the value of type record type itself,
    -- which is the last argument of each projection ("self").  We have
    -- a 'TermVar' here (and after) precisely because we're scoping over
    -- the self element after the tycon parameters above.
    -> [Name]
    -- ^ Names of the remaining fields.
    -> Tel.ProxyTel (Type t) (TermVar v)
    -- ^ Telescope holding the types of the next fields, scoped
    -- over the types of the previous fields.
    -> TC' t ()
addProjections tyCon tyConPars self fields0 =
    go $ zip fields0 $ map Field [0,1..]
  where
    go fields fieldTypes = case (fields, fieldTypes) of
      ([], Tel.Empty Tel.Proxy) ->
        return ()
      ((field, ix) : fields', Tel.Cons (_, fieldType) fieldTypes') -> do
        endType <- (`piTC` fieldType) =<< ctxAppTC (def tyCon []) tyConPars
        addProjection field ix tyCon (Tel.idTel tyConPars endType)
        (go fields' <=< liftTermM . Tel.instantiate fieldTypes') =<< appTC (Var self) [Proj field ix]
      (_, _) -> error "impossible.addProjections: impossible: lengths do not match"

-- TODO what about pattern coverage?

checkFunDef :: (IsTerm t) => Name -> [A.Clause] -> TC' t ()
checkFunDef fun synClauses = do
    funType <- definitionType =<< getDefinition fun
    clauses <- forM synClauses $ \(A.Clause synPats synClauseBody) -> do
      checkPatterns fun synPats funType $ \ctx pats _ clauseType -> do
        clauseBody <- check ctx synClauseBody clauseType
        Clause pats <$> liftTermM (substMap (toIntVar ctx) clauseBody)
    inv <- checkInvertibility clauses
    addClauses fun inv
  where
    toIntVar ctx v = B $ Ctx.elemIndex v ctx

checkPatterns
    :: (IsVar v, IsTerm t, Typeable a)
    => Name
    -> [A.Pattern]
    -> Type t v
    -- ^ Type of the clause that has the given 'A.Pattern's in front.
    -> (∀ v'. (IsVar v') => Ctx.Ctx v (Type t) v' -> [Pattern] -> [Term t v'] -> Type t v' -> TC' t a)
    -- ^ Handler taking a context into the internal variable, list of
    -- internal patterns, a list of terms produced by them, and the type
    -- of the clause body (scoped over the pattern variables).
    -> TC' t a
checkPatterns _ [] type_ ret =
    ret Ctx.Empty [] [] type_
checkPatterns funName (synPat : synPats) type0 ret = atSrcLoc synPat $ do
  stuck <- matchPi_ type0 $ \dom cod -> fmap NotStuck $ do
    checkPattern funName synPat dom $ \ctx pat patVar -> do
      -- TODO remove the substMap
      cod'  <- liftTermM $ substMap (fmap (Ctx.weakenVar ctx)) cod
      cod'' <- liftTermM $ instantiate cod' patVar
      checkPatterns funName synPats cod'' $ \ctx' pats patsVars bodyType -> do
        patVar' <- liftTermM $ Ctx.weaken ctx' patVar
        ret (ctx Ctx.++ ctx') (pat : pats) (patVar' : patsVars) bodyType
  checkPatternStuck funName stuck

checkPattern
    :: (IsVar v, IsTerm t, Typeable a)
    => Name
    -> A.Pattern
    -> Type t v
    -- ^ Type of the matched thing.
    -> (∀ v'. (IsVar v') => Ctx.Ctx v (Type t) v' -> Pattern -> Term t v' -> TC' t a)
    -- ^ Handler taking the context, the internal 'Pattern', and a
    -- 'Term' containing the term produced by it.
    -> TC' t a
checkPattern funName synPat type_ ret = case synPat of
    A.VarP name -> do
      ret (Ctx.singleton name type_) VarP =<< varTC (boundTermVar name)
    A.WildP _ -> do
      ret (Ctx.singleton "_" type_) VarP =<< varTC (boundTermVar "_")
    A.ConP dataCon synPats -> do
      DataCon typeCon dataConType <- getDefinition dataCon
      typeConDef <- getDefinition typeCon
      case typeConDef of
        Constant (Data _)     _ -> return ()
        Constant (Record _ _) _ -> checkError $ PatternMatchOnRecord synPat typeCon
        _                       -> do doc <- prettyDefinitionTC typeConDef
                                      error $ "impossible.checkPattern " ++ render doc
      stuck <- matchTyCon typeCon type_ $ \typeConArgs -> fmap NotStuck $ do
        dataConTypeNoPars <- liftTermM $ Tel.substs (subst'Vacuous dataConType) typeConArgs
        checkPatterns funName synPats dataConTypeNoPars $ \ctx pats patsVars _ -> do
          t <- conTC dataCon patsVars
          ret ctx (ConP dataCon pats) t
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
  :: (IsVar v, IsTerm t)
  => Ctx t v -> A.Expr -> Type t v -> TC' t (Term t v)
check ctx synT type_ = atSrcLoc synT $ case synT of
  A.Con dataCon synArgs -> do
    DataCon tyCon dataConType <- getDefinition dataCon
    metaVarIfStuck ctx type_ $ matchTyCon tyCon type_ $ \tyConArgs -> do
      appliedDataConType <- liftTermM $ Tel.substs (subst'Vacuous dataConType) tyConArgs
      checkConArgs ctx synArgs appliedDataConType `bindStuckTC`
        WaitingOn (con dataCon)
  A.Refl _ -> do
    metaVarIfStuck ctx type_ $ matchEqual type_ $ \type' t1 t2 -> do
      checkEqual ctx type' t1 t2 `bindStuckTC` WaitingOn (\() -> return refl)
  A.Meta _ ->
    addMetaVarInCtx ctx type_
  A.Lam name synBody -> do
    metaVarIfStuck ctx type_ $ matchPi name type_ $ \dom cod -> do
      body <- check (Ctx.Snoc ctx (name, dom)) synBody cod
      returnStuckTC =<< lamTC body
  _ -> do
    metaVarIfStuck ctx type_ $
      infer ctx synT `bindStuckTC` CheckEqualInfer ctx type_

    -- -- TODO Use combinators below, remove duplication with
    -- -- `metaVarIfStuck'.
    -- case stuck of
    --   NotStuck (t, type') -> do
    --     stuck' <- equalType type_ type'
    --     case stuck' of
    --       NotStuck () -> do
    --         return t
    --       StuckOn pid -> do
    --         mv <- addMetaVarInCtx type_
    --         void $ bindProblemCheckEqual pid type' mv t
    --         return mv
    --   StuckOn pid -> do
    --     mv <- addMetaVarInCtx type_
    --     void $ bindProblem pid (WaitForInfer synT type_) $ \(t, type') -> do
    --       stuck' <- equalType type_ type'
    --       case stuck' of
    --         NotStuck () ->
    --           checkEqual type_ mv t
    --         StuckOn pid' ->
    --           StuckOn <$> bindProblemCheckEqual pid' type_ mv t
    --     return mv


checkSpine
  :: (IsVar v, IsTerm t)
  => Ctx t v -> Term t v -> [A.Elim] -> Type t v -> StuckTC' t (Term t v, Type t v)
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
  :: (IsVar v, IsTerm t)
  => Ctx t v -> [A.Expr] -> Type t v -> StuckTC' t [t v]
checkConArgs _ [] _ = do
  returnStuckTC []
checkConArgs ctx (synArg : synArgs) type_ = atSrcLoc synArg $ do
  matchPi_ type_ $ \dom cod -> do
    arg <- check ctx synArg dom
    cod' <- liftTermM $ instantiate cod arg
    checkConArgs ctx synArgs cod' `bindStuckTC` WaitingOn (return . (arg :))

isType :: (IsVar v, IsTerm t) => Ctx t v -> A.Expr -> TC' t (Type t v)
isType ctx abs = check ctx abs set

-- Inference
------------

infer
  :: (IsVar v, IsTerm t)
  => Ctx t v -> A.Expr -> StuckTC' t (Term t v, Type t v)
infer ctx synT = atSrcLoc synT $ case synT of
  A.Set _ ->
    returnStuckTC (set, set)
  A.Pi name synDomain synCodomain -> do
    domain   <- isType ctx synDomain
    codomain <- isType (Ctx.Snoc ctx (name, domain)) synCodomain
    t <- piTC domain codomain
    returnStuckTC (t, set)
  A.Fun synDomain synCodomain -> do
    infer ctx $ A.Pi "_" synDomain synCodomain
  A.App synH elims -> do
    (h, type_) <- inferHead ctx synH
    h' <- appTC h []
    checkSpine ctx h' elims type_
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
  :: (IsVar v, IsTerm t)
  => Ctx t v -> A.Head -> TC' t (Head v, Type t v)
inferHead ctx synH = atSrcLoc synH $ case synH of
  A.Var name -> do
    mbV <- liftTermM $ Ctx.lookupName name ctx
    case mbV of
      Nothing         -> checkError $ NameNotInScope name
      Just (v, type_) -> return (Var v, type_)
  A.Def name -> do
    type_ <- substVacuous <$> (definitionType =<< getDefinition name)
    return (Def name, type_)
  A.J{} -> do
    (J, ) <$> typeOfJ

-- (A : Set) ->
-- (x : A) ->
-- (y : A) ->
-- (P : (x : A) -> (y : A) -> (eq : _==_ A x y) -> Set) ->
-- (p : (x : A) -> P x x refl) ->
-- (eq : _==_ A x y) ->
-- P x y eq
typeOfJ :: forall t v. (IsVar v, IsTerm t) => TC' t (Type t v)
typeOfJ =
  liftTermM $ substMap close =<<
    ("A", return set) -->
    ("x", var "A") -->
    ("y", var "A") -->
    ("P", ("x", var "A") --> ("y", var "A") -->
          ("eq", join (equal <$> var "A" <*> var "x" <*> var "y")) -->
          return set
    ) -->
    ("p", ("x", var "A") --> (app (Var "P") . map Apply =<< sequence [var "x", var "x", return refl])) -->
    ("eq", join (equal <$> var "A" <*> var "x" <*> var "y")) -->
    (app (Var "P") . map Apply =<< sequence [var "x", var "y", return refl])
  where
    close v = error $ "impossible.typeOfJ: Free variable " ++ PP.render v

    infixr 9 -->
    (-->) :: (Name, TermM (t Name)) -> TermM (t Name) -> TermM (t Name)
    (x, type_) --> t = do
      type' <- type_
      t' <- t
      pi type' =<< abstract x t'

-- Equality
------------

checkEqual
  :: (IsVar v, IsTerm t)
  => Ctx t v -> Type t v -> Term t v -> Term t v -> StuckTC' t ()
checkEqual ctx type_ x y = do
  typeView <- whnfViewTC type_
  type' <- unviewTC typeView
  expand <- etaExpand typeView
  blockedX <- whnfTC =<< expand x
  blockedY <- whnfTC =<< expand y
  x' <- liftTermM $ ignoreBlocking blockedX
  y' <- liftTermM $ ignoreBlocking blockedY
  eq <- liftTermM $ termEq x' y'
  case (blockedX, blockedY) of
    (_, _) | eq ->
      returnStuckTC ()
    (MetaVarHead mv elims, _) ->
      metaAssign ctx type_ mv elims y'
    (_, MetaVarHead mv elims) ->
      metaAssign ctx type_ mv elims x'
    (BlockedOn mvs1 _ _, BlockedOn mvs2 _ _) -> do
      -- Both blocked, and we already checked for syntactic equality: we
      -- give up.
      newProblem (HS.union mvs1 mvs2) $ CheckEqual ctx type_ x' y'
    (BlockedOn mvs f elims, _) -> do
      checkEqualBlockedOn ctx type' mvs f elims y'
    (_, BlockedOn mvs f elims) -> do
      checkEqualBlockedOn ctx type' mvs f elims x'
    (NotBlocked _, NotBlocked _) -> do
       xView <- viewTC x'
       yView <- viewTC y'
       case (typeView, xView, yView) of
         -- Note that here we rely on canonical terms to have canonical
         -- types, and on the terms to be eta-expanded.
         (Pi dom cod, Lam body1, Lam body2) -> do
           -- TODO there is a bit of duplication between here and expansion.
           name <- liftTermM $ getAbsName_ body1
           checkEqual (Ctx.Snoc ctx (name, dom)) cod body1 body2
         (Set, Pi dom1 cod1, Pi dom2 cod2) -> do
           name <- liftTermM $ getAbsName_ cod1
           checkEqual ctx set dom1 dom2 `bindStuckTC`
             CheckEqual (Ctx.Snoc ctx (name, dom1)) set cod1 cod2
         (Set, Equal type1 x1 y1, Equal type2 x2 y2) -> do
           checkEqual ctx set type1 type2 `bindStuckTC`
             CheckEqual ctx type1 x1 x2   `bindStuckTC`
             CheckEqual ctx type1 y1 y2
         (_, Refl, Refl) -> do
           returnStuckTC ()
         (App (Def _) tyConPars0, Con dataCon dataConArgs1, Con dataCon' dataConArgs2)
             | Just tyConPars <- mapM isApply tyConPars0
             , dataCon == dataCon' -> do
               DataCon _ dataConType <- getDefinition dataCon
               appliedDataConType <- liftTermM $ Tel.substs (subst'Vacuous dataConType) tyConPars
               equalConArgs ctx appliedDataConType dataCon dataConArgs1 dataConArgs2
         (Set, Set, Set) -> do
           returnStuckTC ()
         (_, App h1 elims1, App h2 elims2) | h1 == h2 -> do
           equalSpine ctx h1 elims1 elims2
         (_, _, _) -> do
           checkError $ TermsNotEqual x y
  where
    etaExpand typeView =
      case typeView of
        App (Def tyCon) _ -> do
          tyConDef <- getDefinition tyCon
          return $ case tyConDef of
            Constant (Record dataCon projs) _ ->
              \t -> do
                ts <- mapM (\(n, ix) -> Apply <$> eliminateTC t [Proj n ix]) projs
                defTC dataCon ts
            _ ->
              return
        Pi _ codomain -> do
          name <- liftTermM $ getAbsName_ codomain
          v <- varTC $ boundTermVar name
          return $ \t -> do
            tView <- whnfViewTC t
            case tView of
              Lam _ -> return t
              _     -> do t' <- liftTermM $ weaken t
                          lamTC =<< eliminateTC t' [Apply v]
        _ ->
          return return

checkEqualSpine
  :: (IsVar v, IsTerm t)
  => Ctx t v
  -> Type t v
  -- ^ Type of the head.
  -> Term t v
  -- ^ Head.
  -> [Elim (Term t) v]
  -> [Elim (Term t) v]
  -> StuckTC' t ()
checkEqualSpine _ _ _ [] [] =
  returnStuckTC ()
checkEqualSpine ctx type_ h (elim1 : elims1) (elim2 : elims2) = do
  case (elim1, elim2) of
    (Apply arg1, Apply arg2) -> do
      typeView <- whnfViewTC type_
      case typeView of
        Pi domain codomain -> do
          -- If you're stuck on the domain, don't give up, and put a
          -- metavariable instead.
          arg1' <- metaVarIfStuck ctx domain $
            checkEqual ctx domain arg1 arg2 `bindStuckTC` WaitingOn (\() -> return arg1)
          h' <- eliminateTC h [Apply arg1']
          codomain' <- liftTermM $ instantiate codomain arg1'
          checkEqualSpine ctx codomain' h' elims1 elims2
        _ -> do
          doc <- prettyTermTC type_
          error $ "impossible.checkEqualSpine: Expected function type " ++ render doc
    (Proj proj projIx, Proj proj' projIx')
      | proj == proj' && projIx == projIx' ->
        applyProjection proj h type_ `bindStuckTC`
          CheckEqualSpine ctx elims1 elims2
    _ ->
      checkError $ SpineNotEqual type_ (elim1 : elims1) (elim1 : elims2)
checkEqualSpine _ type_ _ elims1 elims2 = do
  checkError $ SpineNotEqual type_ elims1 elims2

equalSpine
  :: (IsVar v, IsTerm t)
  => Ctx t v -> Head v -> [Elim t v] -> [Elim t v] -> StuckTC' t ()
equalSpine ctx h elims1 elims2 = do
  hType <- case h of
    Var v   -> liftTermM $ Ctx.getVar v ctx
    Def f   -> substVacuous <$> (definitionType =<< getDefinition f)
    J       -> typeOfJ
    Meta mv -> substVacuous <$> getMetaVarType mv
  h' <- appTC h []
  checkEqualSpine ctx hType h' elims1 elims2

-- | INVARIANT: the two lists are the of the same length.
equalConArgs
  :: (IsVar v, IsTerm t)
  => Ctx t v
  -> Type t v
  -- ^ Type of the head.
  -> Name -> [Term t v] -> [Term t v] -> StuckTC' t ()
equalConArgs ctx type_ dataCon xs ys = do
  expandedCon <- unrollPi type_ $ \ctx' _ ->
                 ctxLamTC ctx' =<< conTC dataCon =<< mapM varTC (ctxVars ctx')
  checkEqualSpine ctx type_ expandedCon (map Apply xs) (map Apply ys)

checkEqualBlockedOn
  :: forall t v.
     (IsVar v, IsTerm t)
  => Ctx t v
  -> Type t v
  -> HS.HashSet MetaVar -> Name -> [Elim t v]
  -> Term t v
  -> StuckTC' t ()
checkEqualBlockedOn ctx type_ mvs fun1 elims1 t2 = do
  t1 <- ignoreBlockingTC $ BlockedOn mvs fun1 elims1
  Function _ clauses <- getDefinition fun1
  case clauses of
    NotInvertible _ -> do
      fallback t1
    Invertible injClauses1 -> do
      t2View <- whnfViewTC t2
      case t2View of
        App (Def fun2) elims2 | fun1 == fun2 -> do
          equalSpine ctx (Def fun1) elims1 elims2
        _ -> do
          t2Head <- termHead =<< unviewTC t2View
          case t2Head of
            Nothing -> do
              fallback t1
            Just tHead | Just (Clause pats _) <- lookup tHead injClauses1 -> do
              -- Make the eliminators match the patterns
              matchPats pats elims1
              -- And restart
              checkEqual ctx type_ t1 t2
            Just _ -> do
              checkError $ TermsNotEqual t1 t2
  where
    fallback t1 = newProblem mvs $ CheckEqual ctx type_ t1 t2

    matchPats :: [Pattern] -> [Elim t v] -> TC' t ()
    matchPats [] [] = do
      return ()
    matchPats (VarP : pats) (_ : elims) = do
      matchPats pats elims
    matchPats (ConP dataCon pats' : pats) (elim : elims) = do
      matchPat dataCon pats' elim
      matchPats pats elims
    matchPats [] _ = do
      -- Less patterns than arguments is fine.
      return ()
    matchPats _ [] = do
      -- Less arguments than patterns is not fine -- we know that the
      -- eliminators were blocked on the patterns.
      error "impossible.checkEqualBlockedOn: got too few patterns."

    matchPat :: Name -> [Pattern] -> Elim t v -> TC' t ()
    matchPat dataCon pats (Apply t) = do
      tView <- whnfViewTC t
      case tView of
        App (Meta mv) mvArgs -> do
          mvT <- substVacuous <$> instantiateDataCon mv dataCon
          matchPat dataCon pats . Apply =<< eliminateTC mvT mvArgs
        Con dataCon' dataConArgs | dataCon == dataCon' ->
          matchPats pats (map Apply dataConArgs)
        _ -> do
          -- This can't happen -- we know that the execution was
          -- blocked, or in other words it was impeded only by
          -- metavariables.
          matchPatErr dataCon pats $ Apply t
    matchPat dataCon pats elim = do
      -- Same as above.
      matchPatErr dataCon pats elim

    matchPatErr dataCon pats elim = do
      doc <- prettyElimTC elim
      error $ "impossible.matchPat: bad elim:\n" ++
              show (ConP dataCon pats) ++ "\n" ++ render doc

equalType :: (IsVar v, IsTerm t) => Ctx t v -> Type t v -> Type t v -> StuckTC' t ()
equalType ctx a b = checkEqual ctx set a b

-- Unification
------------------------------------------------------------------------

metaAssign
  :: (IsVar v, IsTerm t)
  => Ctx t v -> Type t v -> MetaVar -> [Elim (Term t) v] -> Term t v
  -> StuckTC' t ()
metaAssign ctx0 type0 mv elims0 t0 = do
  -- Try to eta-expand the metavariable first.
  mvType <- getMetaVarType mv
  -- If you can, eta-expand and restart the equality.  Otherwise, try to
  -- assign.
  mbRecordDataCon <- unrollPi mvType $ \_ mvEndType -> runMaybeT $ do
    App (Def tyCon) _ <- lift $ whnfViewTC mvEndType
    Constant (Record dataCon _) _ <- lift $ getDefinition tyCon
    return dataCon
  case mbRecordDataCon of
    Just dataCon -> do
      mvT <- substVacuous <$> instantiateDataCon mv dataCon
      mvT' <- eliminateTC mvT elims0
      checkEqual ctx0 type0 mvT' t0
    Nothing -> do
      etaExpandVars ctx0 elims0 (Tel.Prod2 type0 t0) $ \ctx elims (Tel.Prod2 type_ t) -> do
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
                newProblem mvs $ CheckEqual ctx type_ mvT t
              Just mvT -> do
                mvT' <- eliminateTC (substVacuous mvT) elims'
                checkEqual ctx type_ mvT' t'
          Right inv -> do
            t1 <- pruneTerm (Set.fromList $ invertMetaVars inv) t
            t2 <- applyInvertMeta inv t1
            case t2 of
              TTOK t' -> do
                mvs <- metaVarsTC t'
                when (mv `HS.member` mvs) $
                  checkError $ OccursCheckFailed mv t'
                instantiateMetaVar mv t'
                returnStuckTC ()
              TTMetaVars mvs -> do
                mvT <- metaVarTC mv elims
                newProblem (HS.insert mv mvs) $ CheckEqual ctx type_ mvT t
              TTFail v ->
                checkError $ FreeVariableInEquatedTerm mv elims t v

-- | The term must be in normal form.
--
-- Returns the pruned term.
pruneTerm
    :: (IsVar v, IsTerm t)
    => Set.Set v                -- ^ allowed vars
    -> Term t v
    -> TC' t (Term t v)
pruneTerm vs t = do
  tView <- whnfViewTC t
  case tView of
    Lam body -> do
      name <- liftTermM $ getAbsName_ body
      lamTC =<< pruneTerm (addVar name) body
    Pi domain codomain -> do
      name <- liftTermM $ getAbsName_ codomain
      join $ piTC <$> pruneTerm vs domain <*> pruneTerm (addVar name) codomain
    Equal type_ x y -> do
      join $ equalTC <$> pruneTerm vs type_ <*> pruneTerm vs x <*> pruneTerm vs y
    App (Meta mv) elims -> do
      mbMvT <- prune vs mv elims
      case mbMvT of
        Nothing  -> metaVarTC mv elims
        Just mvT -> eliminateTC (substVacuous mvT) elims
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

    addVar name = Set.insert (boundTermVar name) (Set.mapMonotonic F vs)

-- | Prunes a 'MetaVar' application and instantiates the new body.
-- Returns the the new body of the metavariable if we managed to prune
-- anything.
--
-- The term must be in normal form.
prune
    :: forall t v0.
       (IsVar v0, IsTerm t)
    => Set.Set v0               -- ^ allowed vars
    -> MetaVar
    -> [Elim (Term t) v0]       -- ^ Arguments to the metavariable
    -> TC' t (Maybe (Closed (Term t)))
prune allowedVs oldMv elims | Just args <- mapM isApply elims =
  runMaybeT $ go args
  where
    go args = do
      -- TODO check that newly created meta is well-typed.
      kills0 <- MaybeT $ sequence <$> mapM (shouldKill allowedVs) args
      guard $ or kills0
      oldMvType <- lift $ getMetaVarType oldMv
      (newMvType, kills1) <- lift $ createNewMeta oldMvType kills0
      guard $ any unNamed kills1
      newMv <- lift $ addMetaVar =<< telPiTC newMvType
      mvT <- lift $ createMetaLam newMv kills1
      lift $ instantiateMetaVar oldMv mvT
      return mvT

    -- We build a telescope with only the non-killed types in.  This
    -- way, we can analyze the dependency between arguments and avoid
    -- killing things that later arguments depend on.
    --
    -- At the end of the telescope we put both the new metavariable and
    -- the remaining type, so that this dependency check will be
    -- performed on it as well.
    createNewMeta
      :: (IsVar v)
      => Type t v -> [Bool] -> TC' t (Tel.IdTel (Type t) v, [Named Bool])
    createNewMeta type_ [] =
      return (Tel.Empty (Tel.Id type_), [])
    createNewMeta type_ (kill : kills) = do
      typeView <- whnfViewTC type_
      case typeView of
        Pi domain codomain -> do
          name <- liftTermM $ getAbsName_ codomain
          (tel, kills') <- createNewMeta codomain kills
          let notKilled = (Tel.Cons (name, domain) tel, named name False : kills')
          if not kill
            then return notKilled
            else do
              mbTel <- liftTermM $ telStrengthen tel
              return $ case mbTel of
                Nothing   -> notKilled
                Just tel' -> (tel', named name True : kills')
        _ ->
          error "impossible.createPrunedMeta: metavar type too short"

    createMetaLam :: MetaVar -> [Named Bool] -> TC' t (Closed (Type t))
    createMetaLam newMv = go' []
      where
        go' :: [v] -> [Named Bool] -> TC' t (Type t v)
        go' vs [] =
          metaVarTC newMv . map Apply =<< mapM varTC (reverse vs)
        go' vs (kill : kills) =
          let vs' = (if unNamed kill then [] else [B (() <$ kill)]) ++ map F vs
          in lamTC =<< go' vs' kills
prune _ _ _ = do
  -- TODO we could probably do something more.
  return Nothing

-- | Returns whether the term should be killed, given a set of allowed
-- variables.
shouldKill
  :: (IsTerm t, IsVar v)
  => Set.Set v -> Term t v -> TC' t (Maybe Bool)
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


data InvertMeta t v0 =
  forall v. (IsVar v) => InvertMeta [(v0, t v)] [v]
  -- A substitution from variables of the term on the left of the
  -- equation to variables inside the metavar.
  --
  -- We also keep an ordered list of variables to abstract the body of
  -- the metavariable.

invertMetaVars :: InvertMeta t v0 -> [v0]
invertMetaVars (InvertMeta sub _) = map fst sub

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
  :: forall v0 t.
     (IsVar v0, IsTerm t)
  => [Elim (Term t) v0]
  -> TC' t (TermTraverse () (InvertMeta t v0))
invertMeta elims0 = case mapM isApply elims0 of
    Just args0 -> go args0 ([] :: [v0]) (length args0)
    Nothing    -> return $ TTFail ()
  where
    -- First we build up a list of variables representing the bound
    -- arguments in the metavar body.
    go :: (IsVar v)
       => [Term t v0] -> [v] -> Int -> TC' t (TermTraverse () (InvertMeta t v0))
    go args vs 0 = do
      let vs' = reverse vs
      -- Then we try to invert passing pairs of arguments to the
      -- metavariable and bound arguments of the body of the
      -- metavariable.
      res <- checkArgs . zip args =<< mapM varTC vs'
      return $ case res of
        TTFail ()      -> TTFail ()
        TTMetaVars mvs -> TTMetaVars mvs
        -- If we're good, we also check that each variable gets
        -- substituted with only one thing.
        TTOK sub       -> InvertMeta <$> checkLinearity sub <*> pure vs'
    go args vs n =
      go args (boundTermVar "_" : map F vs) (n - 1)

    checkArgs :: [(Term t v0, Term t v)] -> TC' t (TermTraverse () [(v0, Term t v)])
    checkArgs xs = do
      res <- mapM (uncurry checkArg) xs
      return $ concat <$> sequenceA res

    checkArg :: Term t v0 -> Term t v -> TC' t (TermTraverse () [(v0, Term t v)])
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
              DataCon tyCon _ <- getDefinition dataCon
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

    checkLinearity :: [(v0, Term t v)] -> TermTraverse () [(v0, Term t v)]
    checkLinearity sub =
      traverse makeLinear $ groupBy ((==) `on` fst) $ sortBy (comparing fst) sub

    makeLinear :: [(v0, Term t v)] -> TermTraverse () (v0, Term t v)
    makeLinear []      = error "impossible.checkPatternCondition"
    makeLinear [x]     = pure x
    -- TODO Consider making this work for singleton types.
    makeLinear (_ : _) = TTFail ()

applyInvertMeta
  :: forall t v0.
     (IsVar v0, IsTerm t)
  => InvertMeta t v0 -> Term t v0
  -> TC' t (TermTraverse v0 (Closed (Term t)))
applyInvertMeta (InvertMeta sub vs) t = do
  tt <- applyInvertMetaSubst sub t
  case tt of
    TTFail v ->
      return $ TTFail v
    TTMetaVars mvs ->
      return $ TTMetaVars mvs
    TTOK t0 -> do
      t1 <- lambdaAbstract vs t0
      t2 <- liftTermM $ substMap kill t1
      return $ TTOK t2
  where
    kill = error "applyInvertMeta.impossible"

-- | Creates a term in the same context as the original term but lambda
-- abstracted over the given variables.
lambdaAbstract :: (IsVar v, IsTerm t) => [v] -> Term t v -> TC' t (Term t v)
lambdaAbstract []       t = return t
lambdaAbstract (v : vs) t = (lamTC <=< abstractTC v <=< lambdaAbstract vs) t

applyInvertMetaSubst
  :: forall t v0 mvV.
     (IsVar v0, IsVar mvV, IsTerm t)
  => [(v0, t mvV)] -> Term t v0 -> TC' t (TermTraverse v0 (Term t mvV))
applyInvertMetaSubst sub t0 =
  flip go t0 $ \v -> return $ maybe (Left v) Right (lookup v sub)
  where
    lift' :: forall v v1.
             (v -> TC' t (Either v0 (Term t v1)))
          -> (TermVar v -> TC' t (Either v0 (Term t (TermVar v1))))
    lift' _ (B v) = Right <$> varTC (B v)
    lift' f (F v) = do
      e <- f v
      case e of
        Left v' -> return $ Left v'
        Right t -> Right <$> (liftTermM (weaken t))

    go :: forall v v1. (IsVar v, IsVar v1)
       => (v -> TC' t (Either v0 (Term t v1))) -> Term t v -> TC' t (TermTraverse v0 (t v1))
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

data EtaExpandVars t f v = EtaExpandVars [Elim f v] (t f v)

instance (Subst' t) => Subst' (EtaExpandVars t) where
  subst' (EtaExpandVars elims t) f =
    EtaExpandVars <$> mapM (\x -> subst' x f) elims <*> subst' t f

etaExpandVars
  :: (IsVar v, IsTerm f, Subst' t)
  => Ctx.ClosedCtx f v
  -> [Elim f v]
  -> t f v
  -> (forall v'. (IsVar v') => Ctx.ClosedCtx f v' -> [Elim f v'] -> t f v' -> TC' f a)
  -> TC' f a
etaExpandVars ctx0 elims0 t ret = do
  elims <- mapM (etaContractElim <=< nf'TC) elims0
  mbVar <- collectProjectedVar elims
  case mbVar of
    Nothing ->
      ret ctx0 elims t
    Just (v, tyCon) ->
      splitContext ctx0 v (EtaExpandVars elims t) $ \ctx1 type_ tel -> do
        tel' <- etaExpandVar tyCon type_ tel
        Tel.unTel tel' $ \ctx2 (EtaExpandVars elims' t') ->
          etaExpandVars (ctx1 Ctx.++ ctx2) elims' t' ret

-- | Expands a record-typed variable ranging over the given 'Tel.Tel',
-- returning a new telescope ranging over all the fields of the record
-- type and the old telescope with the variable substituted with a
-- constructed record.
etaExpandVar
  :: (IsVar v, IsTerm f, Subst' t)
  => Name
  -- ^ The type constructor of the record type.
  -> Type f v
  -- ^ The type of the variable we're expanding.
  -> Tel.Tel t f (TermVar v)
  -> TC' f (Tel.Tel t f v)
etaExpandVar tyCon type_ tel = do
  Constant (Record dataCon projs) _ <- getDefinition tyCon
  DataCon _ dataConType <- getDefinition dataCon
  App (Def _) tyConPars0 <- whnfViewTC type_
  let Just tyConPars = mapM isApply tyConPars0
  appliedDataConType <- liftTermM $ Tel.substs (subst'Vacuous dataConType) tyConPars
  -- TODO this should be an assertion (unrollPiWithNamesTC must not fail)
  unrollPiWithNames appliedDataConType (map fst projs) $ \dataConPars _ -> do
    tel' <- liftTermM $ subst' tel $ \v -> case v of
      B _  -> con dataCon =<< mapM var (ctxVars dataConPars)
      F v' -> var $ Ctx.weakenVar dataConPars v'
    return $ dataConPars Tel.++ tel'

-- | Scans a list of 'Elim's looking for an 'Elim' composed of projected
-- variable.
collectProjectedVar
  :: (IsVar v, IsTerm t) => [Elim t v] -> TC' t (Maybe (v, Name))
collectProjectedVar elims = runMaybeT $ do
  (v, projName) <- msum $ flip map elims $ \elim -> do
    Apply t <- return elim
    App (Var v) vElims <- lift $ whnfViewTC t
    projName : _ <- forM vElims $ \vElim -> do
      Proj projName _ <- return vElim
      return projName
    return (v, projName)
  tyConDef <- lift $ getDefinition projName
  let Projection _ tyCon _ = tyConDef
  return (v, tyCon)

splitContext
  :: forall t f v0 a.
     Ctx.ClosedCtx f v0
  -> v0
  -> t f v0
  -> (forall v'. (IsVar v') => Ctx.ClosedCtx f v' -> Type f v' -> Tel.Tel t f (TermVar v') -> TC' f a)
  -> TC' f a
splitContext ctx0 v0 t ret = go ctx0 v0 (Tel.Empty t)
  where
    go :: Ctx.ClosedCtx f v -> v -> Tel.Tel t f v -> TC' f a
    go Ctx.Empty                 v     _   = absurd v
    go (Ctx.Snoc ctx (_, type_)) (B _) tel = ret ctx type_ tel
    go (Ctx.Snoc ctx type_)      (F v) tel = go ctx v (Tel.Cons type_ tel)

-- Eta-contraction of terms
---------------------------

etaContractElim :: (IsVar v, IsTerm t) => Elim t v -> TC' t (Elim t v)
etaContractElim (Apply t)  = Apply <$> etaContract t
etaContractElim (Proj n f) = return $ Proj n f

etaContract :: (IsVar v, IsTerm t) => t v -> TC' t (t v)
etaContract t0 = fmap (fromMaybe t0) $ runMaybeT $ do
  t0View <- lift $ whnfViewTC t0
  case t0View of
    -- TODO it should be possible to do it also for constructors
    Lam body -> do
      App h elims@(_:_) <- lift $ whnfViewTC =<< etaContract body
      Apply t <- return $ last elims
      App (Var (B _)) [] <- lift $ whnfViewTC t
      Just t' <- lift $ liftTermM $ strengthen =<< app h (init elims)
      return t'
    Con dataCon args -> do
      DataCon tyCon _ <- lift $ getDefinition dataCon
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
  :: (IsVar v, IsTerm t)
  => Ctx t v -> Type t v -> TC' t (Term t v)
addMetaVarInCtx ctx type_ = do
  mv <- addMetaVar =<< ctxPiTC ctx type_
  ctxAppTC (metaVar mv []) ctx

createMvsPars
  :: (IsVar v, IsTerm t) => Ctx t v -> Tel.IdTel (Type t) v -> TC' t [Term t v]
createMvsPars _ (Tel.Empty _) =
  return []
createMvsPars ctx (Tel.Cons (_, type') tel) = do
  mv  <- addMetaVarInCtx ctx type'
  mvs <- createMvsPars ctx =<< liftTermM (Tel.instantiate tel mv)
  return (mv : mvs)

-- Problem handling
------------------------------------------------------------------------

data TypeCheckProblem (t :: * -> *) a b where
  WaitingOn :: (a -> TermM b) -> TypeCheckProblem t a b

  CheckEqual1     :: (IsVar v)
                  => Ctx t v -> Type t v -> Term t v
                  -> TypeCheckProblem t (Term t v) ()
  CheckEqualInfer :: (IsVar v)
                  => Ctx t v -> Type t v
                  -> TypeCheckProblem t (Term t v, Type t v) (Term t v)
  CheckSpine      :: (IsVar v)
                  => Ctx t v -> [A.Elim]
                  -> TypeCheckProblem t (Term t v, Type t v) (Term t v, Type t v)
  CheckEqual      :: (IsVar v)
                  => Ctx t v -> Type t v -> Term t v -> Term t v
                  -> TypeCheckProblem t () ()
  CheckEqualSpine :: (IsVar v)
                  => Ctx t v
                  -> [Elim (Term t) v] -> [Elim (Term t) v]
                  -> TypeCheckProblem t (Term t v, Type t v) ()

  MatchPi     :: (IsVar v)
              => Name -> Type t v
              -> (Type t v -> Abs (Type t) v -> StuckTC' t a)
              -> TypeCheckProblem t () a
  MatchEqual  :: (IsVar v)
              => Type t v
              -> (Type t v -> Term t v -> Term t v -> StuckTC' t a)
              -> TypeCheckProblem t () a
  MatchTyCon  :: (IsVar v)
              => Name -> Type t v
              -> ([Term t v] -> StuckTC' t a)
              -> TypeCheckProblem t () a

typeCheckProblem
  :: (IsTerm t, Typeable a, Typeable b)
  => TypeCheckProblem t a b -> a -> StuckTC' t b
typeCheckProblem (WaitingOn f) x =
  returnStuckTC =<< liftTermM (f x)
typeCheckProblem (CheckEqual1 ctx type_ t1) t2 =
  checkEqual ctx type_ t1 t2
typeCheckProblem (CheckEqualInfer ctx type_) (t, type') = do
  checkEqual ctx set type_ type' `bindStuckTC` WaitingOn (\() -> return t)
typeCheckProblem (CheckSpine ctx els) (h', type') = do
  checkSpine ctx h' els type'
typeCheckProblem (CheckEqual ctx type_ x y) () = do
  checkEqual ctx type_ x y
typeCheckProblem (CheckEqualSpine ctx elims1 elims2) (h', type') = do
  checkEqualSpine ctx type' h' elims1 elims2
typeCheckProblem (MatchPi n type_ handler) () =
  matchPi n type_ handler
typeCheckProblem (MatchEqual type_ handler) () =
  matchEqual type_ handler
typeCheckProblem (MatchTyCon n type_ handler) () =
  matchTyCon n type_ handler

metaVarIfStuck
  :: (IsTerm t, IsVar v)
  => Ctx t v -> Type t v -> StuckTC' t (Term t v)
  -> TC' t (Term t v)
metaVarIfStuck ctx type_ m = do
    stuck <- m
    case stuck of
      NotStuck t ->
        return t
      StuckOn pid -> do
        mv <- addMetaVarInCtx ctx type_
        void $ bindProblem pid $ CheckEqual1 ctx type_ mv
        return mv

elimStuckTC :: StuckTC' t a -> TC' t a -> TC' t a
elimStuckTC m ifStuck = do
    stuck <- m
    case stuck of
      NotStuck x   -> return x
      StuckOn _pid -> ifStuck

-- Utils
------------------------------------------------------------------------

-- Matching terms
-----------------

matchTyCon
  :: (IsVar v, IsTerm t, Typeable a)
  => Name
  -> Type t v
  -> ([Term t v] -> StuckTC' t a)
  -> StuckTC' t a
matchTyCon tyCon t0 handler = do
  blockedT <- whnfTC t0
  t <- ignoreBlockingTC blockedT
  mbRes <- runMaybeT $ case blockedT of
    NotBlocked _ -> do
      App (Def tyCon') tyConArgs0 <- lift $ whnfViewTC t
      guard (tyCon == tyCon')
      tyConArgs <- MaybeT $ return $ mapM isApply tyConArgs0
      lift $ handler tyConArgs
    MetaVarHead mv _ -> lift $ do
      mvType <- getMetaVarType mv
      mvT <- unrollPi mvType $ \ctxMvArgs _ -> do
        Constant _ tyConType <- getDefinition tyCon
        tyConParsTel <- unrollPi (substVacuous tyConType) $ \ctx -> return . Tel.idTel ctx
        tyConPars <- createMvsPars ctxMvArgs tyConParsTel
        ctxLamTC ctxMvArgs =<< defTC tyCon (map Apply tyConPars)
      instantiateMetaVar mv mvT
      -- TODO Dangerous recursion, relying on correct instantiation.
      -- Maybe remove and do it explicitly?
      matchTyCon tyCon t handler
    BlockedOn mvs _ _ -> lift $ do
      newProblem mvs (MatchTyCon tyCon t handler)
  maybe (checkError $ DataConTypeError tyCon t) return mbRes

matchPi
  :: (IsVar v, IsTerm t, Typeable a)
  => Name                       -- ^ Name for the bound var in the codomain.
  -> Type t v
  -> (Type t v -> Abs (Type t) v -> StuckTC' t a)
  -> StuckTC' t a
matchPi name t0 handler = do
  blockedT <- whnfTC t0
  t <- ignoreBlockingTC blockedT
  mbRes <- runMaybeT $ case blockedT of
    NotBlocked _ -> do
      Pi dom cod <- lift $ whnfViewTC t
      lift $ handler dom cod
    MetaVarHead mv _ -> lift $ do
      mvType <- getMetaVarType mv
      mvT <- unrollPi mvType $ \ctxMvArgs _ -> do
        dom <- addMetaVarInCtx ctxMvArgs set
        cod <- addMetaVarInCtx (Ctx.Snoc ctxMvArgs (name, dom)) set
        ctxLamTC ctxMvArgs =<< piTC dom cod
      instantiateMetaVar mv mvT
      -- TODO Dangerous recursion, relying on correct instantiation.
      -- Maybe remove and do it explicitly?
      matchPi name t handler
    BlockedOn mvs _ _ -> lift $ do
      newProblem mvs (MatchPi name t handler)
  maybe (checkError $ ExpectedFunctionType t Nothing) return mbRes

matchPi_
  :: (IsVar v, IsTerm t, Typeable a)
  => Type t v
  -> (Type t v -> Abs (Type t) v -> StuckTC' t a)
  -> StuckTC' t a
matchPi_ = matchPi "_"

matchEqual
  :: (IsVar v, IsTerm t, Typeable a)
  => Type t v
  -> (Type t v -> Term t v -> Term t v -> StuckTC' t a)
  -> StuckTC' t a
matchEqual t0 handler = do
  blockedT <- whnfTC t0
  t <- ignoreBlockingTC blockedT
  mbRes <- runMaybeT $ case blockedT of
    NotBlocked _ -> do
      Equal type_ t1 t2 <- lift $ whnfViewTC t
      lift $ handler type_ t1 t2
    MetaVarHead mv _ -> lift $ do
      mvType <- getMetaVarType mv
      mvT <- unrollPi mvType $ \ctxMvArgs _ -> do
        type_ <- addMetaVarInCtx ctxMvArgs set
        t1 <- addMetaVarInCtx ctxMvArgs type_
        t2 <- addMetaVarInCtx ctxMvArgs type_
        ctxLamTC ctxMvArgs =<< equalTC type_ t1 t2
      instantiateMetaVar mv mvT
      matchEqual t handler
    BlockedOn mvs _ _ -> lift $ do
      newProblem mvs (MatchEqual t handler)
  maybe (checkError $ ExpectedEqual t) return mbRes

applyProjection
  :: (IsVar v, IsTerm t)
  => Name
  -- ^ Name of the projection
  -> Term t v
  -- ^ Head
  -> Type t v
  -- ^ Type of the head
  -> StuckTC' t (Term t v, Type t v)
applyProjection proj h type_ = do
  Projection projIx tyCon projType <- getDefinition proj
  h' <- eliminateTC h [Proj proj projIx]
  matchTyCon tyCon type_ $ \tyConArgs -> do
    appliedProjType <- liftTermM $ Tel.substs (subst'Vacuous projType) tyConArgs
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
  mvT <- unrollPi mvType $ \ctxMvArgs endType' -> do
    DataCon tyCon dataConTypeTel <- getDefinition dataCon
    -- We know that the metavariable must have the right type (we have
    -- typechecked the arguments already).
    App (Def tyCon') tyConArgs0 <- whnfViewTC endType'
    Just tyConArgs <- return $ mapM isApply tyConArgs0
    True <- return $ tyCon == tyCon'
    dataConType <- liftTermM $ Tel.substs (subst'Vacuous dataConTypeTel) tyConArgs
    dataConArgsTel <- unrollPi dataConType $ \ctx -> return . Tel.idTel ctx
    dataConArgs <- createMvsPars ctxMvArgs dataConArgsTel
    ctxLamTC ctxMvArgs =<< conTC dataCon dataConArgs
  instantiateMetaVar mv mvT
  return mvT

-- Whnf'ing and view'ing
------------------------

nfTC :: (IsVar v, IsTerm t) => t v -> TC t v' (t v)
nfTC t = withSignatureTermM $ \sig -> nf sig t

nf'TC :: (IsVar v, IsTerm t, Nf f) => f t v -> TC t v' (f t v)
nf'TC t = withSignatureTermM $ \sig -> nf' sig t

whnfTC :: (IsVar v, IsTerm t) => t v -> TC t v' (Blocked t v)
whnfTC t = withSignatureTermM $ \sig -> whnf sig t

whnfViewTC :: (IsVar v, IsTerm t) => t v -> TC t v' (TermView t v)
whnfViewTC t = withSignatureTermM $ \sig -> whnfView sig t

viewTC :: (IsVar v, IsTerm t) => t v -> TC t v' (TermView t v)
viewTC t = liftTermM $ view t

-- Unrolling Pis
----------------

-- TODO remove duplication

unrollPiWithNames
  :: (IsVar v, IsTerm t)
  => Type t v
  -- ^ Type to unroll
  -> [Name]
  -- ^ Names to give to each parameter
  -> (∀ v'. (IsVar v') => Ctx.Ctx v (Type t) v' -> Type t v' -> TC' t a)
  -- ^ Handler taking a context with accumulated domains of the pis
  -- and the final codomain.
  -> TC' t a
unrollPiWithNames type_ [] ret =
  ret Ctx.Empty type_
unrollPiWithNames type_ (name : names) ret = do
  typeView <- whnfViewTC type_
  case typeView of
    Pi domain codomain ->
      unrollPiWithNames codomain names $ \ctxVs endType ->
      ret (Ctx.singleton name domain Ctx.++ ctxVs) endType
    _ ->
      checkError $ ExpectedFunctionType type_ Nothing

unrollPi
  :: (IsVar v, IsTerm t)
  => Type t v
  -- ^ Type to unroll
  -> (∀ v'. (IsVar v') => Ctx.Ctx v (Type t) v' -> Type t v' -> TC' t a)
  -- ^ Handler taking a weakening function, the list of domains
  -- of the unrolled pis, the final codomain.
  -> TC' t a
unrollPi type_ ret = do
  typeView <- whnfViewTC type_
  case typeView of
    Pi domain codomain -> do
      name <- liftTermM $ getAbsName_ codomain
      unrollPi codomain $ \ctxVs endType ->
        ret (Ctx.singleton name domain Ctx.++ ctxVs) endType
    _ ->
      ret Ctx.Empty type_

-- Errors
---------

data CheckError t
    = ∀ v. (IsVar v) => DataConTypeError Name (Type t v)
    | ∀ v. (IsVar v) => LambdaTypeError A.Expr (Type t v)
    | ∀ v. (IsVar v) => NotEqualityType (Type t v)
    | ∀ v. (IsVar v) => ExpectedFunctionType (Type t v) (Maybe A.Expr)
    | CannotInferTypeOf A.Expr
    | ∀ v. (IsVar v) => TermsNotEqual (Term t v) (Term t v)
    | ∀ v. (IsVar v) => SpineNotEqual (Type t v) [Elim t v] [Elim t v]
    | ∀ v. (IsVar v) => ExpectingRecordType (Type t v)
    | ∀ v. (IsVar v) => FreeVariableInEquatedTerm MetaVar [Elim t v] (Term t v) v
    | PatternMatchOnRecord A.Pattern
                           Name -- Record type constructor
    | ∀ v. (IsVar v) => MismatchingPattern (Type t v) A.Pattern
    | OccursCheckFailed MetaVar (Closed (Term t))
    | ∀ v. (IsVar v) => ExpectedEqual (Term t v)
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
      return $ "Free variable `" <> prettyVar v <> "' in term equated to metavariable application:" $$
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
      return $ "Got stuck on the type signature when checking clauses for function `" <> PP.pretty name <> "'"
    ClausesAlreadyAdded fun -> do
      return $ "Clauses already added for function `" <> PP.pretty fun <> "'"
  where
    prettyVar :: forall v. (IsVar v) => v -> PP.Doc
    prettyVar = PP.pretty . varName

-- Clauses invertibility
------------------------

termHead :: (IsTerm t, IsVar v) => t v -> TC' t (Maybe TermHead)
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

telStrengthen :: (IsTerm f) => Tel.IdTel f (TermVar v) -> TermM (Maybe (Tel.IdTel f v))
telStrengthen (Tel.Empty (Tel.Id t)) =
  fmap (Tel.Empty . Tel.Id) <$> strengthen t
telStrengthen (Tel.Cons (n, t) tel0) = runMaybeT $ do
  t' <- MaybeT $ strengthen t
  tel' <- MaybeT $ telStrengthen tel0
  return $ Tel.Cons (n, t') tel'

-- | Collects all the variables in the 'Ctx.Ctx'.
ctxVars :: IsTerm t => Ctx.Ctx v0 (Type t) v -> [v]
ctxVars = reverse . go
  where
    go :: IsTerm t => Ctx.Ctx v0 (Type t) v -> [v]
    go Ctx.Empty                = []
    go (Ctx.Snoc ctx (name, _)) = boundTermVar name : map F (go ctx)

-- | Creates a 'Pi' type containing all the types in the 'Ctx' and
-- terminating with the provided 't'.
ctxPi :: IsTerm t => Ctx.Ctx v0 (Type t) v -> Type t v -> TermM (Type t v0)
ctxPi Ctx.Empty                  t = return t
ctxPi (Ctx.Snoc ctx (_n, type_)) t = ctxPi ctx =<< pi type_ t

-- | Creates a 'Lam' term with as many arguments there are in the
-- 'Ctx.Ctx'.
ctxLam :: IsTerm t => Ctx.Ctx v0 (Type t) v -> Term t v -> TermM (Term t v0)
ctxLam Ctx.Empty        t = return t
ctxLam (Ctx.Snoc ctx _) t = ctxLam ctx =<< lam t

-- Monad versions of signature-requiring things
-----------------------------------------------

ctxAppTC :: (IsTerm t, IsVar v) => TermM (Term t v) -> Ctx.Ctx v0 (Type t) v -> TC' t (Term t v)
ctxAppTC t ctx0 = do
  t' <- liftTermM t
  eliminateTC t' . map Apply =<< mapM varTC (ctxVars ctx0)

eliminateTC :: IsTerm t => t v -> [Elim t v] -> TC' t (t v)
eliminateTC h els = withSignatureTermM $ \sig -> eliminate sig h els

freeVarsTC :: (IsTerm t, IsVar v) => t v -> TC' t (FreeVars v)
freeVarsTC t = withSignatureTermM $ \sig -> freeVars sig t

metaVarsTC :: IsTerm t => t v -> TC' t (HS.HashSet MetaVar)
metaVarsTC t = withSignatureTermM $ \sig -> metaVars sig t

prettyTermTC :: (IsVar v, IsTerm t) => t v -> TC' t PP.Doc
prettyTermTC t = withSignatureTermM $ \sig -> prettyTerm sig t

prettyElimTC :: (IsVar v, IsTerm t) => Elim t v -> TC' t PP.Doc
prettyElimTC t = withSignatureTermM $ \sig -> prettyElim sig t

prettyElimsTC :: (IsVar v, IsTerm t) => [Elim t v] -> TC' t PP.Doc
prettyElimsTC es = withSignatureTermM $ \sig -> prettyElims sig es

prettyDefinitionTC :: (IsTerm t) => Closed (Definition t) -> TC' t PP.Doc
prettyDefinitionTC def' = withSignatureTermM $ \sig -> prettyDefinition sig def'

unviewTC :: IsTerm t => TermView t v -> TC' t (t v)
unviewTC = liftTermM . unview

lamTC :: IsTerm t => Abs t v -> TC' t (t v)
lamTC body = liftTermM $ unview $ Lam body

piTC :: IsTerm t => t v -> Abs t v -> TC' t  (t v)
piTC domain codomain = liftTermM $ unview $ Pi domain codomain

equalTC :: IsTerm t => t v -> t v -> t v -> TC' t (t v)
equalTC type_ x y = liftTermM $ unview $ Equal type_ x y

appTC :: IsTerm t => Head v -> [Elim t v] -> TC' t  (t v)
appTC h elims = liftTermM $ unview $ App h elims

metaVarTC :: IsTerm t => MetaVar -> [Elim t v] -> TC' t (t v)
metaVarTC mv = liftTermM . unview . App (Meta mv)

defTC :: IsTerm t => Name -> [Elim t v] -> TC' t (t v)
defTC f = liftTermM . unview . App (Def f)

conTC :: IsTerm t => Name -> [t v] -> TC' t (t v)
conTC c args = liftTermM $ unview (Con c args)

varTC :: IsTerm t => v -> TC' t (t v)
varTC = liftTermM . var

ctxLamTC :: IsTerm t => Ctx.Ctx v0 (Type t) v -> Term t v -> TC' t (Term t v0)
ctxLamTC ctx = liftTermM . ctxLam ctx

ctxPiTC :: IsTerm t => Ctx.Ctx v0 (Type t) v -> Type t v -> TC' t (Type t v0)
ctxPiTC ctx = liftTermM . ctxPi ctx

telPiTC :: (IsVar v, IsTerm t) => Tel.IdTel (Type t) v -> TC' t (Type t v)
telPiTC tel = Tel.unTel tel $ \ctx endType -> ctxPiTC ctx (Tel.unId endType)

ignoreBlockingTC :: (IsTerm t) => Blocked t v -> TC' t (t v)
ignoreBlockingTC = liftTermM . ignoreBlocking

abstractTC :: (IsTerm t, Eq v, VarName v) => v -> t v -> TC' t (Abs t v)
abstractTC v = liftTermM . abstract v

-- Miscellanea
--------------

isApply :: Elim (Term t) v -> Maybe (Term t v)
isApply (Apply v) = Just v
isApply Proj{}    = Nothing

definitionType :: (IsTerm t) => Closed (Definition t) -> TC' t (Closed (Type t))
definitionType (Constant _ type_)   = return type_
definitionType (DataCon _ tel)      = telPiTC tel
definitionType (Projection _ _ tel) = telPiTC tel
definitionType (Function type_ _)   = return type_

isRecordType :: (IsTerm t) => Name -> TC' t Bool
isRecordType tyCon = withSignature $ \sig ->
  case Sig.getDefinition sig tyCon of
    Constant (Record _ _) _ -> True
    _                       -> False

isRecordConstr :: (IsTerm t) => Name -> TC' t Bool
isRecordConstr dataCon = join $ withSignature $ \sig ->
  case Sig.getDefinition sig dataCon of
    DataCon tyCon _ -> isRecordType tyCon
    _               -> return False
