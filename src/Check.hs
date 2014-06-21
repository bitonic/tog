{-# LANGUAGE OverloadedStrings #-}
module Check (checkProgram) where

import           Prelude                          hiding (abs, pi)

import           Data.Functor                     ((<$>), (<$))
import           Data.Foldable                    (forM_, toList, Foldable)
import qualified Data.HashSet                     as HS
import           Control.Monad                    (when, void, guard, mzero, forM, msum)
import           Data.List                        (sortBy, groupBy)
import           Data.Traversable                 (traverse, sequenceA, Traversable)
import           Prelude.Extras                   ((==#))
import           Bound                            hiding (instantiate, abstract)
import           Bound.Var                        (unvar)
import           Data.Typeable                    (Typeable)
import           Data.Void                        (vacuous, Void, vacuousM, absurd)
import qualified Data.Set                         as Set
import qualified Data.Map                         as Map
import           Control.Applicative              (Applicative(pure, (<*>)))
import           Control.Monad.Trans              (lift)
import           Control.Monad.Trans.Either       (EitherT(EitherT), runEitherT)
import           Control.Monad.Trans.Maybe        (MaybeT(MaybeT), runMaybeT)
import           Data.Function                    (on)
import           Data.Ord                         (comparing)

import           Syntax.Abstract                  (Name)
import           Syntax.Abstract.Pretty           ()
import qualified Syntax.Abstract                  as A
import           Types.Definition
import qualified Types.Context                    as Ctx
import qualified Types.Telescope                  as Tel
import           Types.Monad
import           Types.Term
import           Text.PrettyPrint.Extended        (render, (<+>), ($$))
import qualified Text.PrettyPrint.Extended        as PP
import qualified Types.Signature                  as Sig
import           Eval
import           FreeVars

-- Main functions
------------------------------------------------------------------------

-- Type checking
----------------

check :: (IsVar v, IsTerm t) => A.Expr -> Type t v -> TC t v (Term t v)
check synT type_ = atSrcLoc synT $ case synT of
  A.Con dataCon synArgs -> do
    DataCon tyCon dataConType <- getDefinition dataCon
    let err = DataConTypeError synT type_
    metaVarIfStuck type_ $ matchTyCon tyCon type_ err $ \tyConArgs -> do
      let appliedDataConType = Tel.substs (vacuous dataConType) tyConArgs
      bindStuckTC (checkConArgs synArgs appliedDataConType) WaitingOn $ \args ->
        notStuck $ con dataCon args
  A.Refl _ -> do
    let err = NotEqualityType type_
    metaVarIfStuck type_ $ matchEqual type_ err  $ \type' t1 t2 -> do
      bindStuckTC (checkEqual type' t1 t2) WaitingOn $ \() ->
        notStuck refl
  A.Meta _ ->
    addMetaVarInCtx type_
  A.Lam name synBody -> do
    let err = LambdaTypeError synT type_
    metaVarIfStuck type_ $ matchPi name type_ err  $ \dom cod -> do
      body <- extendContext name dom $ \_ -> check synBody (fromAbs cod)
      notStuck $ lam (toAbs body)
  _ -> do
    stuck <- infer synT
    -- TODO Use combinators below, remove duplication with
    -- `metaVarIfStuck'.
    case stuck of
      NotStuck (t, type') -> do
        stuck' <- equalType type_ type'
        case stuck' of
          NotStuck () -> do
            return t
          StuckOn pid -> do
            mv <- addMetaVarInCtx type_
            void $ bindProblemCheckEqual pid type' mv t
            return mv
      StuckOn pid -> do
        mv <- addMetaVarInCtx type_
        void $ bindProblem pid (WaitForInfer synT type_) $ \(t, type') -> do
          stuck' <- equalType type_ type'
          case stuck' of
            NotStuck () ->
              checkEqual type_ mv t
            StuckOn pid' ->
              StuckOn <$> bindProblemCheckEqual pid' type_ mv t
        return mv

isType :: (IsVar v, IsTerm t) => A.Expr -> TC t v (Type t v)
isType abs = check abs set

checkConArgs :: (IsVar v, IsTerm t) => [A.Expr] -> Type t v -> StuckTC t v [t v]
checkConArgs []                 _     = notStuck []
checkConArgs (synArg : synArgs) type_ = atSrcLoc synArg $ do
  let err = ExpectedFunctionType type_ (Just synArg)
  matchPi_ type_ err $ \dom cod -> do
    arg <- check synArg dom
    bindStuckTC (checkConArgs synArgs (instantiate cod arg)) WaitingOn $ \args ->
      notStuck (arg : args)

infer :: (IsVar v, IsTerm t) => A.Expr -> StuckTC t v (Term t v, Type t v)
infer synT = atSrcLoc synT $ case synT of
  A.Set _ ->
    notStuck (set, set)
  A.Pi name synDomain synCodomain -> do
    domain   <- isType synDomain
    codomain <- extendContext name domain $ \_ -> isType synCodomain
    notStuck (pi domain (toAbs codomain), set)
  A.Fun synDomain synCodomain -> do
    domain   <- isType synDomain
    codomain <- isType synCodomain
    notStuck (pi domain (weaken codomain), set)
  A.App synH elims -> do
    (h, type_) <- inferHead synH
    checkSpine (unview (App h [])) elims type_
  A.Equal synType synX synY -> do
    type_ <- isType synType
    x <- check synX type_
    y <- check synY type_
    notStuck (equal type_ x y, set)
  _ -> do
    type_ <- addMetaVarInCtx set
    t <- check synT type_
    notStuck (t, type_)

checkSpine :: (IsVar v, IsTerm t)
           => Term t v -> [A.Elim] -> Type t v -> StuckTC t v (Term t v, Type t v)
checkSpine h []         type_ = notStuck (h, type_)
checkSpine h (el : els) type_ = atSrcLoc el $ case el of
  A.Proj proj -> do
    bindStuckTC (applyProjection proj h type_) (\_ -> CheckSpine h (el :els) type_) $
      \(h', type') -> checkSpine h' els type'
  A.Apply synArg -> do
    let err = ExpectedFunctionType type_ (Just synArg)
    matchPi_ type_ err $ \dom cod -> do
      arg <- check synArg dom
      let cod' = instantiate cod arg
      let h' = eliminate h [Apply arg]
      checkSpine h' els cod'

inferHead :: (IsVar v, IsTerm t) => A.Head -> TC t v (Head v, Type t v)
inferHead synH = atSrcLoc synH $ case synH of
  A.Var name -> do
    mbType <- getTypeOfName name
    case mbType of
      Nothing         -> checkError $ NameNotInScope name
      Just (v, type_) -> return (Var v, type_)
  A.Def name -> do
    type_ <- definitionType <$> getDefinition name
    return (Def name, vacuous type_)
  A.J{} ->
    return (J, vacuous $ typeOfJ)

-- Equality
-----------

checkEqual :: (IsVar v, IsTerm t) => Type t v -> Term t v -> Term t v -> StuckTC t v ()
checkEqual _ x y | x ==# y =
  notStuck ()
checkEqual type_ x y = do
  typeView <- whnfViewTC type_
  expand <- etaExpand typeView
  blockedX <- whnfTC $ expand x
  blockedY <- whnfTC $ expand y
  case (blockedX, blockedY) of
    (_, _) | blockedX ==# blockedY ->
      notStuck ()
    (MetaVarHead mv elims, t) ->
      metaAssign type_ mv elims (ignoreBlocking t)
    (t, MetaVarHead mv elims) ->
      metaAssign type_ mv elims (ignoreBlocking t)
    (BlockedOn mvs1 _ _, BlockedOn mvs2 _ _) -> do
      -- Both blocked, we give up and check only syntactic equality.
      x' <- nfTC $ ignoreBlocking blockedX
      y' <- nfTC $ ignoreBlocking blockedY
      if x' ==# y'
        then notStuck ()
        else fmap StuckOn $
               newProblemCheckEqual
                 (Set.union mvs1 mvs2) (unview typeView)
                 (ignoreBlocking blockedX) (ignoreBlocking blockedY)
    (BlockedOn mvs f elims, t) -> do
      checkEqualBlockedOn (unview typeView) mvs f elims (ignoreBlocking t)
    (t, BlockedOn mvs f elims) -> do
      checkEqualBlockedOn (unview typeView) mvs f elims (ignoreBlocking t)
    (NotBlocked x', NotBlocked y') -> case (typeView, view x', view y') of
      -- Note that here we rely on canonical terms to have canonical
      -- types, and on the terms to be eta-expanded.
      (Pi dom cod, Lam body1, Lam body2) -> do
        -- TODO there is a bit of duplication between here and expansion.
        let body1' = fromAbs body1
        let body2' = fromAbs body2
        let cod'   = fromAbs cod
        extendContext (getName_ body1') dom $ \_ ->
          checkEqual cod' body1' body2'
      (Set, Pi dom1 cod1, Pi dom2 cod2) -> do
        let cod1' = fromAbs cod1
        bindStuckTC (checkEqual set dom1 dom2) (\_ -> CheckEqual set dom1 dom2) $ \() ->
          extendContext (getName_ cod1') dom1 $ \_ ->
            checkEqual set cod1' (fromAbs cod2)
      (Set, Equal type1 x1 y1, Equal type2 x2 y2) ->
        bindStuckTC (checkEqual set type1 type2) (\_ -> CheckEqual type1 x1 x2) $ \() ->
        bindStuckTC (checkEqual type1 x1 x2)     (\_ -> CheckEqual type1 y1 y2) $ \() ->
        checkEqual type1 y1 y2
      (_, Refl, Refl) -> do
        notStuck ()
      (App (Def _) tyConPars0, Con dataCon dataConArgs1, Con dataCon' dataConArgs2)
          | Just tyConPars <- mapM isApply tyConPars0
          , dataCon == dataCon' -> do
            DataCon _ dataConType <- getDefinition dataCon
            let appliedDataConType = Tel.substs (vacuous dataConType) tyConPars
            equalConArgs appliedDataConType dataCon dataConArgs1 dataConArgs2
      (Set, Set, Set) -> do
        notStuck ()
      (_, App h1 elims1, App h2 elims2) | h1 == h2 -> do
        equalSpine h1 elims1 elims2
      (_, _, _) -> do
        checkError $ TermsNotEqual x y
  where
    etaExpand typeView = do
      sig <- getSignature
      case typeView of
        App (Def tyCon) _ | isRecordType sig tyCon -> do
          let Constant (Record dataCon projs) _ = Sig.getDefinition sig tyCon
          return $ \t ->
            def dataCon $ map (\(n, ix) -> Apply (eliminate t [Proj n ix])) projs
        Pi _ codomain -> do
          let name = getName_ $ fromAbs codomain
          let v    = var $ boundTermVar name
          return $ \t ->
            case view t of
              Lam _ -> t
              _     -> lam $ toAbs $ eliminate (fromAbs (weaken t)) [Apply v]
        _ ->
          return id

equalSpine
  :: (IsVar v, IsTerm t) => Head v -> [Elim t v] -> [Elim t v] -> StuckTC t v ()
equalSpine h elims1 elims2 = do
  hType <- case h of
    Var v   -> getTypeOfVar v
    Def f   -> vacuous . definitionType <$> getDefinition f
    J       -> return $ vacuous typeOfJ
    Meta mv -> vacuous <$> getTypeOfMetaVar mv
  checkEqualSpine hType (app h []) elims1 elims2

checkEqualBlockedOn
  :: forall t v.
     (IsVar v, IsTerm t)
  => Type t v
  -> Set.Set MetaVar -> Name -> [Elim t v]
  -> Term t v
  -> StuckTC t v ()
checkEqualBlockedOn type_ mvs fun1 elims1 t2 = do
  Function _ clauses <- getDefinition fun1
  case clauses of
    NotInvertible _ -> do
      fallback
    Invertible injClauses1 -> do
      t2View <- whnfViewTC t2
      case t2View of
        App (Def fun2) elims2 | fun1 == fun2 -> do
          equalSpine (Def fun1) elims1 elims2
        _ -> do
          sig <- getSignature
          case termHead sig (unview t2View) of
            Nothing -> do
              fallback
            Just tHead | Just (Clause pats _) <- lookup tHead injClauses1 -> do
              -- Make the eliminators match the patterns
              matchPats pats elims1
              -- And restart
              checkEqual type_ t1 t2
            Just _ -> do
              checkError $ TermsNotEqual t1 t2
  where
    t1 = ignoreBlocking (BlockedOn mvs fun1 elims1)
    fallback = fmap StuckOn $ newProblemCheckEqual mvs type_ t1 t2

    matchPats :: [Pattern] -> [Elim t v] -> TC t v ()
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

    matchPat :: Name -> [Pattern] -> Elim t v -> TC t v ()
    matchPat dataCon pats (Apply t) = do
      tView <- whnfViewTC t
      case tView of
        App (Meta mv) mvArgs -> do
          mvT <- liftClosed $ instantiateDataCon mv dataCon
          matchPat dataCon pats $ Apply $ eliminate (vacuous mvT) mvArgs
        Con dataCon' dataConArgs | dataCon == dataCon' ->
          matchPats pats (map Apply dataConArgs)
        _ ->
          -- This can't happen -- we know that the execution was
          -- blocked, or in other words it was impeded only by
          -- metavariables.
          error $ "impossible.matchPat: bad elim:\n" ++
                  show (ConP dataCon pats) ++ "\n" ++ render (Apply t)
    matchPat dataCon pats elim = do
      -- Same as above.
      error $ "impossible.matchPat: bad elim:\n" ++
              show (ConP dataCon pats) ++ "\n" ++ render elim

equalType :: (IsVar v, IsTerm t) => Type t v -> Type t v -> StuckTC t v ()
equalType a b = checkEqual set a b

checkEqualSpine
    :: (IsVar v, IsTerm t)
    => Type t v
    -- ^ Type of the head.
    -> Term t v
    -- ^ Head.
    -> [Elim (Term t) v]
    -> [Elim (Term t) v]
    -> StuckTC t v ()
checkEqualSpine _ _ [] [] =
  notStuck ()
checkEqualSpine type_ h (elim1 : elims1) (elim2 : elims2) = do
  let desc = EqualSpine h (elim1 : elims1) (elim2 : elims2) type_
  case (elim1, elim2) of
    (Apply arg1, Apply arg2) -> do
      typeView <- whnfViewTC type_
      case typeView of
        Pi domain codomain -> do
          -- If you're stuck on the domain, don't give up, and put a
          -- metavariable instead.
          arg1' <-
            metaVarIfStuck domain $
              bindStuckTC (checkEqual domain arg1 arg2) (\_ -> desc) $ \() ->
                notStuck arg1
          checkEqualSpine (instantiate codomain arg1') (eliminate h [Apply arg1']) elims1 elims2
        _ ->
          error $ "impossible.checkEqualSpine: Expected function type " ++ render typeView
    (Proj proj projIx, Proj proj' projIx')
      | proj == proj' && projIx == projIx' ->
        bindStuckTC (applyProjection proj h type_) (\_ -> desc) $ \(h', type') ->
          checkEqualSpine type' h' elims1 elims2
    _ ->
      checkError $ SpineNotEqual type_ (elim1 : elims1) (elim1 : elims2)
checkEqualSpine type_ _ elims1 elims2 = do
  checkError $ SpineNotEqual type_ elims1 elims2

-- | INVARIANT: the two lists are the of the same length.
equalConArgs
    :: (IsVar v, IsTerm t)
    => Type t v
    -- ^ Type of the head.
    -> Name -> [Term t v] -> [Term t v] -> StuckTC t v ()
equalConArgs type_ dataCon xs ys = do
  expandedCon <- unrollPiTC type_ $ \ctx _ ->
                 return $ ctxLam ctx $ con dataCon $ map var $ ctxVars ctx
  checkEqualSpine type_ expandedCon (map Apply xs) (map Apply ys)

applyProjection
    :: (IsVar v, IsTerm t)
    => Name
    -- ^ Name of the projection
    -> Term t v
    -- ^ Head
    -> Type t v
    -- ^ Type of the head
    -> StuckTC t v (Term t v, Type t v)
applyProjection proj h type_ = do
  projDef <- getDefinition proj
  case projDef of
    Projection projIx tyCon projType -> do
      let h' = eliminate h [Proj proj projIx]
      let err = ExpectingRecordType type_
      matchTyCon tyCon type_ err $ \tyConArgs -> fmap NotStuck $ do
        let appliedProjType = view $ Tel.substs (vacuous projType) tyConArgs
        case appliedProjType of
          Pi _ endType ->
            return (h', instantiate endType h)
          _ ->
            error $ "impossible.applyProjection: " ++ render appliedProjType
    _ ->
      error $ "impossible.applyProjection: " ++ render projDef

-- MetaVar handling
-------------------

addMetaVarInCtx :: (IsVar v, IsTerm t) => Type t v -> TC t v (Term t v)
addMetaVarInCtx type_ = do
  ctx <- askContext
  mv <- addMetaVar $ ctxPi ctx type_
  return $ ctxApp (metaVar mv []) ctx

metaAssign
  :: (IsVar v, IsTerm t)
  => Type t v -> MetaVar -> [Elim (Term t) v] -> Term t v -> StuckTC t v ()
metaAssign type0 mv elims0 t0 = do
  -- Try to eta-expand the metavariable first.
  mvType <- getTypeOfMetaVar mv
  mbRecordDataCon <- liftClosed $ unrollPiTC mvType $ \_ mvEndType -> do
    sig <- getSignature
    return $ case whnfView sig mvEndType of
      App (Def tyCon) _ | Constant (Record dataCon _) _ <- Sig.getDefinition sig tyCon ->
        Just dataCon
      _ ->
        Nothing
  -- If you can, eta-expand and restart the equality.  Otherwise, try to
  -- assign.
  case mbRecordDataCon of
    Just dataCon -> do
      mvT <- liftClosed $ instantiateDataCon mv dataCon
      checkEqual type0 (eliminate (vacuous mvT) elims0) t0
    Nothing -> do
      sig <- getSignature
      ctx0 <- askContext
      liftClosed $
        etaExpandVars sig ctx0 elims0 (Tel.Prod2 type0 t0) $ \ctx elims (Tel.Prod2 type_ t) ->
          localContext (\_ -> ctx) $ do
            let invOrMvs = case invertMeta sig elims of
                  TTOK inv       -> Right inv
                  TTMetaVars mvs -> Left $ Set.insert mv mvs
                  -- TODO here we should also wait on metavars on the right that
                  -- could simplify the problem.
                  TTFail ()      -> Left $ Set.singleton mv
            case invOrMvs of
              Left mvs -> do
                let t' = nf sig t
                -- TODO should we really prune allowing all variables here?  Or
                -- only the rigid ones?
                let fvs = fvAll $ freeVars sig t'
                pruned <- liftClosed $ prune fvs mv $ map (nf' sig) elims
                if pruned
                  then checkEqual type_ (metaVar mv elims) t
                  else fmap StuckOn $
                         newProblem mvs (CheckEqual type_ (metaVar mv elims) t) $
                           checkEqual type_ (metaVar mv elims) t
              Right inv -> do
                -- TODO have `pruneTerm' return an evaluated term.
                liftClosed $ pruneTerm (Set.fromList $ toList inv) t
                sig' <- getSignature
                case applyInvertMeta sig' inv (nf sig' t) of
                  TTOK t' -> do
                    let mvs = metaVars t'
                    when (mv `HS.member` mvs) $
                      checkError $ OccursCheckFailed mv $ vacuous t'
                    instantiateMetaVar mv t'
                    notStuck ()
                  TTMetaVars mvs ->
                    fmap StuckOn $
                      newProblemCheckEqual (Set.insert mv mvs) type_ (metaVar mv elims) t
                  TTFail v ->
                    checkError $ FreeVariableInEquatedTerm mv elims t v

-- Eta-expansion of arguments of metas
--------------------------------------

data EtaExpandVars t f v = EtaExpandVars [Elim f v] (t f v)

instance (Bound t) => Bound (EtaExpandVars t) where
  EtaExpandVars elims t >>>= f = EtaExpandVars (map (>>>= f) elims) (t >>>= f)

etaExpandVars
  :: (IsVar v, IsTerm f, Bound t)
  => Sig.Signature f
  -> Ctx.ClosedCtx f v
  -> [Elim f v]
  -> t f v
  -> (forall v'. (IsVar v') => Ctx.ClosedCtx f v' -> [Elim f v'] -> t f v' -> a)
  -> a
etaExpandVars sig ctx0 elims0 t ret =
  let elims = map (etaContractElim sig . nf' sig) elims0
  in case collectProjectedVar sig elims of
    Nothing ->
      ret ctx0 elims t
    Just (v, tyCon) ->
      splitContext ctx0 v (EtaExpandVars elims t) $ \ctx1 type_ tel ->
        let tel' = etaExpandVar sig tyCon type_ tel
        in Tel.unTel tel' $ \ctx2 (EtaExpandVars elims' t') ->
           etaExpandVars sig (ctx1 Ctx.++ ctx2) elims' t' ret

-- | Expands a record-typed variable ranging over the given 'Tel.Tel',
-- returning a new telescope ranging over all the fields of the record
-- type and the old telescope with the variable substituted with a
-- constructed record.
etaExpandVar
  :: (IsVar v, IsTerm f, Bound t)
  => Sig.Signature f
  -> Name
  -- ^ The type constructor of the record type.
  -> Type f v
  -- ^ The type of the variable we're expanding.
  -> Tel.Tel t f (TermVar v)
  -> Tel.Tel t f v
etaExpandVar sig tyCon type_ tel =
  let Constant (Record dataCon projs) _ = Sig.getDefinition sig tyCon
      DataCon _ dataConType = Sig.getDefinition sig dataCon
      App (Def _) tyConPars0 = whnfView sig type_
      Just tyConPars = mapM isApply tyConPars0
      appliedDataConType = Tel.substs (vacuous dataConType) tyConPars
      Right tel'' = unrollPiWithNames sig appliedDataConType (map fst projs) $ \dataConPars _ ->
        let tel' = tel >>>= \v -> case v of
                     B _  -> con dataCon $ map var $ ctxVars dataConPars
                     F v' -> var $ Ctx.weaken dataConPars v'
        in dataConPars Tel.++ tel'
  in tel''

-- | Scans a list of 'Elim's looking for an 'Elim' composed of projected
-- variable.
collectProjectedVar
  :: (IsVar v, IsTerm t) => Sig.Signature t -> [Elim t v] -> Maybe (v, Name)
collectProjectedVar sig elims = do
  (v, projName) <- msum $ flip map elims $ \elim -> do
    Apply t <- return elim
    App (Var v) vElims <- return $ whnfView sig t
    projName : _ <- forM vElims $ \vElim -> do
      Proj projName _ <- return vElim
      return projName
    return (v, projName)
  let Projection _ tyCon _ = Sig.getDefinition sig projName
  return (v, tyCon)

splitContext
  :: forall t f v0 a.
     Ctx.ClosedCtx f v0
  -> v0
  -> t f v0
  -> (forall v'. (IsVar v') => Ctx.ClosedCtx f v' -> Type f v' -> Tel.Tel t f (TermVar v') -> a)
  -> a
splitContext ctx0 v0 t ret = go ctx0 v0 (Tel.Empty t)
  where
    go :: Ctx.ClosedCtx f v -> v -> Tel.Tel t f v -> a
    go Ctx.Empty                 v     _   = absurd v
    go (Ctx.Snoc ctx (_, type_)) (B _) tel = ret ctx type_ tel
    go (Ctx.Snoc ctx type_)      (F v) tel = go ctx v (Tel.Cons type_ tel)

-- Eta-contraction of terms
---------------------------

etaContractElim :: (IsVar v, IsTerm t) => Sig.Signature t -> Elim t v -> Elim t v
etaContractElim sig (Apply t)  = Apply $ etaContract sig t
etaContractElim _   (Proj n f) = Proj n f

etaContract :: (IsVar v, IsTerm t) => Sig.Signature t -> t v -> t v
etaContract sig t0 = case whnfView sig t0 of
  -- TODO it should be possible to do it also for constructors
  Lam body
    | App h elims@(_:_) <- whnfView sig (etaContract sig (fromAbs body))
    , Apply t <- last elims
    , App (Var (B _)) [] <- whnfView sig t
    , Just t' <- traverse (unvar (const Nothing) Just) (app h (init elims)) ->
      t'
  Con dataCon args
    | DataCon tyCon _ <- Sig.getDefinition sig dataCon
    , Constant (Record _ fields) _ <- Sig.getDefinition sig tyCon
    , length args == length fields
    , Just (t : ts) <- sequence (zipWith isRightProjection fields args)
    , all (t ==#) ts ->
      t
  _ ->
    t0
  where
    isRightProjection (n, f) t
      | App h elims@(_ : _) <- whnfView sig (etaContract sig t)
      , Proj n' f' <- last elims
      , n == n', f == f' =
        Just $ nf sig $ app h (init elims)
    isRightProjection _ _ =
      Nothing

-- Pruning
----------

-- | The term must be in normal form.
pruneTerm
    :: (IsVar v, IsTerm t)
    => Set.Set v                -- ^ allowed vars
    -> Term t v
    -> ClosedTC t ()
pruneTerm vs t = do
  sig <- getSignature
  case whnfView sig t of
    Lam body -> do
      let body' = fromAbs body
      pruneTerm (Set.insert (boundTermVar (getName_ body')) (Set.mapMonotonic F vs)) body'
    Pi domain codomain -> do
      pruneTerm vs domain
      let codomain' = fromAbs codomain
      pruneTerm (Set.insert (boundTermVar (getName_ codomain')) (Set.mapMonotonic F vs)) codomain'
    Equal type_ x y ->
      mapM_ (pruneTerm vs) [type_, x, y]
    App (Meta mv) elims ->
      void (liftClosed (prune vs mv elims)) >> return ()
    App _ elims ->
      mapM_ (pruneTerm vs) [t' | Apply t' <- elims]
    Set ->
      return ()
    Refl ->
      return ()
    Con _ args ->
      mapM_ (pruneTerm vs) args

-- | Prunes a 'MetaVar' application and instantiates the new body.
-- Returns if some (not necessarely all) pruning was performed.
--
-- The term must be in normal form.
prune
    :: forall t v0.
       (IsVar v0, IsTerm t)
    => Set.Set v0               -- ^ allowed vars
    -> MetaVar
    -> [Elim (Term t) v0]       -- ^ Arguments to the metavariable
    -> ClosedTC t Bool
prune allowedVs oldMv elims | Just args <- mapM isApply elims =
  maybe False (\() -> True) <$> runMaybeT (go args)
  where
    go args = do
      -- TODO check that newly created meta is well-typed.
      sig <- lift $ getSignature
      kills0 <- MaybeT $ return $ mapM (shouldKill sig allowedVs) args
      guard $ or kills0
      oldMvType <- lift $ getTypeOfMetaVar oldMv
      let (newMvType, kills1) = createNewMeta sig oldMvType kills0
      guard $ any unNamed kills1
      newMv <- lift $ addMetaVar $ telPi newMvType
      lift $ instantiateMetaVar oldMv (createMetaLam newMv kills1)

    -- We build a telescope with only the non-killed types in.  This
    -- way, we can analyze the dependency between arguments and avoid
    -- killing things that later arguments depend on.
    --
    -- At the end of the telescope we put both the new metavariable and
    -- the remaining type, so that this dependency check will be
    -- performed on it as well.
    createNewMeta
      :: (IsVar v)
      => Sig.Signature t -> Type t v -> [Bool]
      -> (Tel.IdTel (Type t) v, [Named Bool])
    createNewMeta _ type_ [] =
      (Tel.Empty (Tel.Id type_), [])
    createNewMeta sig type_ (kill : kills) =
      case whnfView sig type_ of
        Pi domain codomain ->
          let codomain' = fromAbs codomain
              name = getName_ codomain'
              (tel, kills') = createNewMeta sig codomain' kills
              notKilled = (Tel.Cons (name, domain) tel, named name False : kills')
          in if not kill
             then notKilled
             else case traverse (unvar (const Nothing) Just) tel of
               Nothing   -> notKilled
               Just tel' -> (tel', named name True : kills')
        _ ->
          error "impossible.createPrunedMeta: metavar type too short"

    createMetaLam :: MetaVar -> [Named Bool] -> Closed (Type t)
    createMetaLam newMv = go' []
      where
        go' :: [v] -> [Named Bool] -> Type t v
        go' vs [] =
          metaVar newMv $ map (Apply . var) (reverse vs)
        go' vs (kill : kills) =
          let vs' = (if unNamed kill then [] else [B (() <$ kill)]) ++ map F vs
          in lam $ toAbs $ go' vs' kills
prune _ _ _ = do
  -- TODO we could probably do something more.
  return False

-- | Returns whether the term should be killed, given a set of allowed
-- variables.
shouldKill
  :: (IsTerm t, IsVar v)
  => Sig.Signature t -> Set.Set v -> Term t v -> Maybe Bool
shouldKill sig vs t = do
  case whnfView sig t of
    Lam _ ->
      mzero
    Con dataCon args | isRecordConstr sig dataCon ->
      and <$> mapM (shouldKill sig vs) args
    App (Def f) _ | not (isNeutral sig f) ->
      mzero
    Con _ _ ->
      mzero
    _ ->
      return $ not (fvRigid (freeVars sig t) `Set.isSubsetOf` vs)

data InvertMeta t v v0
  = IMSubst [(v0, t v)] [v]
  -- A substitution from variables of the term on the left of the
  -- equation to variables inside the metavar.
  --
  -- We also keep an ordered list of variables to abstract the body of
  -- the metavariable.
  | IMArgument (InvertMeta t (TermVar v) v0)
  deriving (Functor, Foldable, Traversable)

-- | Tries to invert a metavariable given its parameters (eliminators),
-- providing a substitution for the term on the right if it suceeds.
-- Doing so amounts to check if the pattern condition is respected for
-- the arguments, although we employ various trick to get around it when
-- the terms are not variables.
--
-- 'TTMetaVars' if the pattern condition check is blocked on a some
-- 'MetaVar's.  The set is empty if the pattern condition is not
-- respected and no 'MetaVar' can change that.
--
-- 'TTFail' if the pattern condition fails.
invertMeta
  :: forall v0 t.
     (IsVar v0, IsTerm t)
  => Sig.Signature t
  -> [Elim (Term t) v0]
  -> TermTraverse () (InvertMeta t v0 v0)
invertMeta sig elims0 = case mapM isApply elims0 of
    Just args0 -> go args0 [] (length args0)
    Nothing    -> TTFail ()     -- TODO eta-expand metavars to eliminate projections.
  where
    go :: [Term t v0] -> [v] -> Int -> TermTraverse () (InvertMeta t v v0)
    go args vs 0 =
      let vs' = reverse vs
      in case checkArgs (zip args (map var vs')) of
           TTFail ()      -> TTFail ()
           TTMetaVars mvs -> TTMetaVars mvs
           TTOK sub       -> IMSubst <$> checkLinearity sub <*> pure vs'
    go args vs n =
      IMArgument <$> go args (boundTermVar "_" : map F vs) (n - 1)

    checkArgs :: [(Term t v0, Term t v)] -> TermTraverse () [(v0, Term t v)]
    checkArgs xs = concat <$> traverse (uncurry checkArg) xs

    checkArg :: Term t v0 -> Term t v -> TermTraverse () [(v0, Term t v)]
    checkArg arg v = case whnf sig arg of
      NotBlocked t
        | App (Var v0) [] <- view t ->
          pure [(v0, v)]
      NotBlocked t
        | Con dataCon recArgs <- view t
        , DataCon tyCon _ <- Sig.getDefinition sig dataCon
        , Constant (Record _ fields) _ <- Sig.getDefinition sig tyCon ->
          checkArgs [ (recArg, eliminate v [Proj n f])
                    | (recArg, (n, f)) <- zip recArgs fields
                    ]
      NotBlocked _ ->
        TTFail ()
      MetaVarHead mv _ ->
        TTMetaVars $ Set.singleton mv
      BlockedOn mvs _ _ ->
        TTMetaVars mvs

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
  => Sig.Signature t -> InvertMeta t v0 v0 -> Term t v0
  -> TermTraverse v0 (Closed (Term t))
applyInvertMeta sig invMeta = go invMeta
  where
    go :: (IsVar v)
       => InvertMeta t v v0 -> Term t v0 -> TermTraverse v0 (Closed (Term t))
    go (IMSubst    sub vs) t = fmap kill . lambdaAbstract vs <$>
                               applyInvertMetaSubst sig sub t
    go (IMArgument im)     t = go im t

    kill = error "applyInvertMeta.impossible"

-- | Creates a term in the same context as the original term but lambda
-- abstracted over the given variables.
lambdaAbstract :: (IsVar v, IsTerm t) => [v] -> Term t v -> Term t v
lambdaAbstract []       t = t
lambdaAbstract (v : vs) t = unview $ Lam $ abstract v $ lambdaAbstract vs t

-- TODO improve efficiency of this traversal, we shouldn't need all
-- those `fromAbs'.  Also in `freeVars'.
applyInvertMetaSubst
    :: forall t v0 mvV.
       (IsVar v0, IsVar mvV, IsTerm t)
    => Sig.Signature t -> [(v0, t mvV)] -> Term t v0
    -> TermTraverse v0 (Term t mvV)
applyInvertMetaSubst sig subst t0 =
  flip go t0 $ \v -> maybe (Left v) Right (lookup v subst)
  where
    lift' :: forall v v1.
             (v -> Either v0 (Term t v1))
          -> (TermVar v -> Either v0 (Term t (TermVar v1)))
    lift' _ (B v) = Right $ var $ B v
    lift' f (F v) = fmap F <$> f v

    go :: forall v v1. (IsVar v, IsVar v1)
       => (v -> Either v0 (Term t v1)) -> Term t v -> TermTraverse v0 (t v1)
    go invert t =
      case whnfView sig t of
        Lam body ->
          (lam . toAbs) <$> go (lift' invert) (fromAbs body)
        Pi dom cod ->
          (\dom' cod' -> pi dom' (toAbs cod'))
            <$> go invert dom <*> go (lift' invert) (fromAbs cod)
        Equal type_ x y ->
          (\type' x' y' -> equal type' x' y')
            <$> (go invert type_) <*> (go invert x) <*> (go invert y)
        Refl ->
          pure refl
        Con dataCon args ->
          con dataCon <$> sequenceA (map (go invert) args)
        Set ->
          pure set
        App h elims ->
          let goElim (Apply t') = Apply <$> go invert t'
              goElim (Proj n f) = pure $ Proj n f

              resElims = traverse goElim elims
          in case (h, resElims) of
               (Meta mv, TTMetaVars mvs) ->
                 TTMetaVars $ Set.insert mv mvs
               (Meta mv, TTFail _) ->
                 TTMetaVars $ Set.singleton mv
               (Var v, _) ->
                 eliminate <$> either TTFail pure (invert v) <*> resElims
               (Def f, _) ->
                 app (Def f) <$> resElims
               (J, _) ->
                 app J <$> resElims
               (Meta mv, _) ->
                 app (Meta mv) <$> resElims

-- Problem handling
-------------------

notStuck :: a -> StuckTC t v a
notStuck x = return $ NotStuck x

metaVarIfStuck
    :: (IsTerm t, IsVar v)
    => Type t v -> StuckTC t v (Term t v)
    -> TC t v (Term t v)
metaVarIfStuck type_ m = do
    stuck <- m
    case stuck of
      NotStuck t ->
        return t
      StuckOn pid -> do
        mv <- addMetaVarInCtx type_
        void $ bindProblem pid (MetaVarIfStuck mv type_ pid) $ checkEqual type_ mv
        return mv

elimStuckTC :: StuckTC t v a -> TC t v a -> TC t v a
elimStuckTC m ifStuck = do
    stuck <- m
    case stuck of
      NotStuck x   -> return x
      StuckOn _pid -> ifStuck

bindStuck
    :: (IsVar v, IsTerm t, Typeable a, Typeable b)
    => Stuck a -> (ProblemId a -> CheckProblem t v)
    -> (a -> StuckTC t v b) -> StuckTC t v b
bindStuck (NotStuck x)  _    f = f x
bindStuck (StuckOn pid) desc f = StuckOn <$> bindProblem pid (desc pid) f

bindStuckTC
    :: (IsVar v, IsTerm t, Typeable a, Typeable b)
    => StuckTC t v a -> (ProblemId a -> CheckProblem t v)
    -> (a -> StuckTC t v b) -> StuckTC t v b
bindStuckTC m desc f = do
    stuck <- m
    bindStuck stuck desc f

-- Checking definitions
------------------------------------------------------------------------

checkProgram
    :: ∀ t. (IsTerm t) => [A.Decl] -> IO (Either TCErr (TCState t))
checkProgram decls0 = do
    drawLine
    putStrLn "-- Checking declarations"
    drawLine
    runEitherT (goDecls initTCState decls0)
  where
    goDecls :: TCState t -> [A.Decl] -> EitherT TCErr IO (TCState t)
    goDecls ts [] = do
      lift $ report ts
      return ts
    goDecls ts (decl : decls) = do
      lift $ putStrLn $ render decl
      ((), ts') <- EitherT $ runTC ts $ checkDecl decl >> solveProblems_
      goDecls ts' decls

    report :: TCState t -> IO ()
    report ts = do
      let tr  = tcReport ts
      let mvsTypes  = Sig.metaVarsTypes $ trSignature tr
      let mvsBodies = Sig.metaVarsBodies $ trSignature tr
      drawLine
      putStrLn $ "-- Solved MetaVars: " ++ show (Map.size mvsBodies)
      putStrLn $ "-- Unsolved MetaVars: " ++ show (Map.size mvsTypes - Map.size mvsBodies)
      drawLine
      forM_ (Map.toList mvsTypes) $ \(mv, mvType) -> do
        putStrLn $ render $
          PP.pretty mv <+> ":" <+> PP.nest 2 (PP.pretty (view mvType))
        let mvBody = case Map.lookup mv mvsBodies of
              Nothing      -> "?"
              Just mvBody0 -> prettyView mvBody0
        putStrLn $ render $ PP.pretty mv <+> "=" <+> PP.nest 2 mvBody
        putStrLn ""
      drawLine
      putStrLn $ "-- Solved problems: " ++ show (Set.size (trSolvedProblems tr))
      putStrLn $ "-- Unsolved problems: " ++ show (Map.size (trUnsolvedProblems tr))
      drawLine
      forM_ (Map.toList (trUnsolvedProblems tr)) $ \(pid, (probState, probDesc)) -> do
        let desc = render $
              PP.pretty pid $$
              PP.nest 2 (PP.pretty probState) $$
              PP.nest 2 probDesc
        putStrLn desc
        putStrLn ""

    drawLine =
      putStrLn "------------------------------------------------------------------------"

checkDecl :: (IsTerm t) => A.Decl -> ClosedTC t ()
checkDecl decl = atSrcLoc decl $ do
  case decl of
    A.TypeSig sig      -> checkTypeSig sig
    A.DataDef d xs cs  -> checkData d xs cs
    A.RecDef d xs c fs -> checkRec d xs c fs
    A.FunDef f clauses -> checkFunDef f clauses

checkTypeSig :: (IsTerm t) => A.TypeSig -> ClosedTC t ()
checkTypeSig (A.Sig name absType) = do
    type_ <- isType absType
    addConstant name Postulate type_

-- Data
-------

checkData
    :: (IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Names of parameters to the tycon.
    -> [A.TypeSig]
    -- ^ Types for the data constructors.
    -> ClosedTC t ()
checkData tyCon tyConPars dataCons = do
    tyConType <- definitionType <$> getDefinition tyCon
    addConstant tyCon (Data []) tyConType
    unrollPiWithNamesTC tyConType tyConPars $ \tyConPars' endType -> do
        elimStuckTC (equalType endType set) $
          error $ "Type constructor does not return Set: " ++ show tyCon
        let appliedTyConType = ctxApp (def tyCon []) tyConPars'
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
    -> TC t v ()
checkConstr tyCon tyConPars appliedTyConType (A.Sig dataCon synDataConType) = do
    atSrcLoc dataCon $ do
        dataConType <- isType synDataConType
        unrollPiTC dataConType $ \vs endType -> do
            let appliedTyConType' = fmap (Ctx.weaken vs) appliedTyConType
            elimStuckTC (equalType appliedTyConType' endType) $ do
              checkError $ TermsNotEqual appliedTyConType' endType
        addDataCon dataCon tyCon (Tel.idTel tyConPars dataConType)

-- Record
---------

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
    -> ClosedTC t ()
checkRec tyCon tyConPars dataCon fields = do
    tyConType <- definitionType <$> getDefinition tyCon
    addConstant tyCon (Record dataCon []) tyConType
    unrollPiWithNamesTC tyConType tyConPars $ \tyConPars' endType -> do
        void $ equalType endType set
        fieldsTel <- checkFields fields
        let appliedTyConType = ctxApp (def tyCon []) tyConPars'
        extendContext (A.name "_") appliedTyConType $ \self -> do
            addProjections
                tyCon tyConPars' self (map A.typeSigName fields) $
                (fmap F fieldsTel)
        Tel.unTel fieldsTel $ \fieldsCtx Tel.Proxy ->
            addDataCon dataCon tyCon $
            Tel.idTel tyConPars' $
            ctxPi fieldsCtx (fmap (Ctx.weaken fieldsCtx) appliedTyConType)

checkFields
    :: (IsVar v, IsTerm t) => [A.TypeSig] -> TC t v (Tel.ProxyTel (Type t) v)
checkFields = go Ctx.Empty
  where
    go :: (IsVar v, IsVar v', IsTerm t)
       => Ctx.Ctx v (Type t) v' -> [A.TypeSig] -> TC t v' (Tel.ProxyTel (Type t) v)
    go ctx [] =
        return $ Tel.proxyTel ctx
    go ctx (A.Sig field synFieldType : fields) = do
        fieldType <- isType synFieldType
        extendContext field fieldType $ \_ ->
            go (Ctx.Snoc ctx (field, fieldType)) fields

addProjections
    :: (IsVar v, IsTerm t)
    => Name
    -- ^ Type constructor.
    -> Ctx.ClosedCtx (Type t) v
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
    -> TC t (TermVar v) ()
addProjections tyCon tyConPars self fields0 =
    go $ zip fields0 $ map Field [0,1..]
  where
    go fields fieldTypes = case (fields, fieldTypes) of
        ([], Tel.Empty Tel.Proxy) ->
            return ()
        ((field, ix) : fields', Tel.Cons (_, fieldType) fieldTypes') -> do
            let endType = pi (ctxApp (def tyCon []) tyConPars) (toAbs fieldType)
            addProjection field ix tyCon (Tel.idTel tyConPars endType)
            go fields' $
                Tel.instantiate fieldTypes' $ unview $ App (Var self) [Proj field ix]
        (_, _) -> error "impossible.addProjections: impossible: lengths do not match"

-- Clause
---------

-- TODO what about pattern coverage?

checkFunDef :: (IsTerm t) => Name -> [A.Clause] -> ClosedTC t ()
checkFunDef fun synClauses = do
    funType <- definitionType <$> getDefinition fun
    clauses <- forM synClauses $ \(A.Clause synPats synClauseBody) -> do
      checkPatterns fun synPats funType $ \_ pats _ clauseType -> do
        clauseBody <- check synClauseBody clauseType
        ctx <- askContext
        return $ Clause pats $ Scope $ fmap (toIntVar ctx) clauseBody
    sig <- getSignature
    addClauses fun $ checkInvertibility sig clauses
  where
    toIntVar ctx v = B $ Ctx.elemIndex v ctx

checkPatterns
    :: (IsVar v, IsTerm t, Typeable a)
    => Name
    -> [A.Pattern]
    -> Type t v
    -- ^ Type of the clause that has the given 'A.Pattern's in front.
    -> (∀ v'. (IsVar v') => (v -> v') -> [Pattern] -> [Term t v'] -> Type t v' -> TC t v' a)
    -- ^ Handler taking a function to weaken an external variable,
    -- list of internal patterns, a list of terms produced by them, and
    -- the type of the clause body (scoped over the pattern variables).
    -> TC t v a
checkPatterns _ [] type_ ret =
    ret id [] [] type_
checkPatterns funName (synPat : synPats) type0 ret = atSrcLoc synPat $ do
  let err = ExpectedFunctionType type0 Nothing
  stuck <- matchPi_ type0 err $ \dom cod -> fmap NotStuck $ do
    checkPattern funName synPat dom $ \weaken_ pat patVar -> do
      let cod'  = fmap weaken_ cod
      let cod'' = instantiate cod' patVar
      checkPatterns funName synPats cod'' $ \weaken_' pats patsVars -> do
        let patVar' = fmap weaken_' patVar
        ret (weaken_' . weaken_) (pat : pats) (patVar' : patsVars)
  checkPatternStuck funName stuck

checkPattern
    :: (IsVar v, IsTerm t, Typeable a)
    => Name
    -> A.Pattern
    -> Type t v
    -- ^ Type of the matched thing.
    -> (∀ v'. (IsVar v') => (v -> v') -> Pattern -> Term t v' -> TC t v' a)
    -- ^ Handler taking a weakening function, the internal 'Pattern',
    -- and a 'Term' containing the term produced by it.
    -> TC t v a
checkPattern funName synPat type_ ret = case synPat of
    A.VarP name ->
      extendContext name type_ $ \v ->
      ret F VarP (var v)
    A.WildP _ ->
      extendContext (A.name "_") type_ $ \v ->
      ret F VarP (var v)
    A.ConP dataCon synPats -> do
      DataCon typeCon dataConType <- getDefinition dataCon
      typeConDef <- getDefinition typeCon
      case typeConDef of
        Constant (Data _)     _ -> return ()
        Constant (Record _ _) _ -> checkError $ PatternMatchOnRecord synPat typeCon
        _                       -> error $ "impossible.checkPattern" ++ render typeConDef
      let err = MismatchingPattern type_ synPat
      stuck <- matchTyCon typeCon type_ err $ \typeConArgs -> fmap NotStuck $ do
        let dataConTypeNoPars = Tel.substs (vacuous dataConType) typeConArgs
        checkPatterns funName synPats dataConTypeNoPars $ \weaken_ pats patsVars _ -> do
          let t = unview (Con dataCon patsVars)
          ret weaken_ (ConP dataCon pats) t
      checkPatternStuck funName stuck

-- TODO we can loosen this by postponing adding clauses.
checkPatternStuck :: (IsVar v, IsTerm t) => Name -> Stuck a -> TC t v a
checkPatternStuck funName stuck =
  case stuck of
    NotStuck x -> return x
    StuckOn _  -> checkError $ StuckTypeSignature funName

-- Clauses invertibility
------------------------

termHead :: (IsTerm t) => Sig.Signature t -> t v -> Maybe TermHead
termHead sig t = case whnfView sig t of
  App (Def f) _ ->
    case Sig.getDefinition sig f of
      Constant Data{}      _ -> Just $ DefHead f
      Constant Record{}    _ -> Just $ DefHead f
      -- TODO here we can't return 'Just' because we don't know if the
      -- postulate is going to be instantiated afterwards.  Ideally we'd
      -- have a "postulate" keyword to avoid this.
      Constant Postulate{} _ -> Nothing
      _                      -> Nothing
  Con f _ ->
    Just $ DefHead f
  Pi _ _ ->
    Just $ PiHead
  _ ->
    Nothing

checkInvertibility
  :: (IsTerm t) => Sig.Signature t -> [Closed (Clause t)] -> Closed (Invertible t)
checkInvertibility sig = go []
  where
    go injClauses [] =
      Invertible $ reverse injClauses
    go injClauses (clause@(Clause _ body) : clauses) =
      case termHead sig (fromScope body) of
        Just tHead | Nothing <- lookup tHead injClauses ->
          go ((tHead, clause) : injClauses) clauses
        _ ->
          NotInvertible $ reverse (map snd injClauses) ++ (clause : clauses)

-- Utils
------------------------------------------------------------------------

-- Unrolling Pis
----------------

-- TODO remove duplication

data SaveContext t v a =
  forall v'. (IsVar v') => SaveContext (Ctx.Ctx v t v') (TC t v' a)

unrollPiWithNames
  :: (IsVar v, IsTerm t)
  => Sig.Signature t
  -> Type t v
  -- ^ Type to unroll
  -> [Name]
  -- ^ Names to give to each parameter
  -> (∀ v'. (IsVar v') => Ctx.Ctx v (Type t) v' -> Type t v' -> a)
  -- ^ Handler taking a context with accumulated domains of the pis
  -- and the final codomain.
  -> Either String a
unrollPiWithNames _ type_ [] ret =
  return $ ret Ctx.Empty type_
unrollPiWithNames sig type_ (name : names) ret =
  case whnfView sig type_ of
    Pi domain codomain ->
      unrollPiWithNames sig (fromAbs codomain) names $ \ctxVs endType ->
      ret (Ctx.singleton name domain Ctx.++ ctxVs) endType
    _ ->
      Left $ renderError sig $ ExpectedFunctionType type_ Nothing

unrollPiWithNamesTC
  :: (IsVar v, IsTerm t) => Type t v -> [Name]
  -> (∀ v'. (IsVar v') => Ctx.Ctx v (Type t) v' -> Type t v' -> TC t v' a)
  -> TC t v a
unrollPiWithNamesTC type_ names ret = do
  sig <- getSignature
  case unrollPiWithNames sig type_ names (\ctx -> SaveContext ctx . ret ctx) of
    Left err ->
      typeError err
    Right (SaveContext ctx m) -> do
      ctx0 <- askContext
      localContext (\_ -> ctx0 Ctx.++ ctx) m

unrollPi
  :: (IsVar v, IsTerm t)
  => Sig.Signature t
  -> Type t v
  -- ^ Type to unroll
  -> (∀ v'. (IsVar v') => Ctx.Ctx v (Type t) v' -> Type t v' -> a)
  -- ^ Handler taking a weakening function, the list of domains
  -- of the unrolled pis, the final codomain.
  -> Either String a
unrollPi sig type_ ret = do
  case whnfView sig type_ of
    Pi domain codomain ->
      let codomain' = fromAbs codomain
          name      = getName_ codomain'
      in unrollPi sig codomain' $ \ctxVs endType ->
         ret (Ctx.singleton name domain Ctx.++ ctxVs) endType
    _ ->
      return $ ret Ctx.Empty type_

unrollPiTC
  :: (IsVar v, IsTerm t)
  => Type t v
  -> (∀ v'. (IsVar v') => Ctx.Ctx v (Type t) v' -> Type t v' -> TC t v' a)
  -> TC t v a
unrollPiTC type_ ret = do
  sig <- getSignature
  case unrollPi sig type_ (\ctx -> SaveContext ctx . ret ctx) of
    Left err ->
      typeError err
    Right (SaveContext ctx m) -> do
      ctx0 <- askContext
      localContext (\_ -> ctx0 Ctx.++ ctx) m

-- Definition utils
-------------------

addConstant
    :: (IsVar v, IsTerm t)
    => Name -> ConstantKind -> Closed (Type t) -> TC t v ()
addConstant x k a = addDefinition x (Constant k a)

addDataCon
    :: (IsVar v, IsTerm t)
    => Name -> Name -> Tel.ClosedIdTel (Type t) -> TC t v ()
addDataCon c d tel = addDefinition c (DataCon d tel)

addProjection
    :: (IsVar v, IsTerm t)
    => Name -> Field -> Name -> Tel.ClosedIdTel (Type t) -> TC t v ()
addProjection f n r tel = addDefinition f (Projection n r tel)

addClauses
    :: (IsVar v, IsTerm t) => Name -> Closed (Invertible t) -> TC t v ()
addClauses f clauses = do
  def' <- getDefinition f
  let ext (Constant Postulate a) = return $ Function a clauses
      ext (Function _ _)         = checkError $ ClausesAlreadyAdded f
      ext (Constant k _)         = error $ "Monad.addClause " ++ render k
      ext DataCon{}              = error $ "Monad.addClause constructor"
      ext Projection{}           = error $ "Monad.addClause projection"
  addDefinition f =<< ext def'

definitionType :: (IsTerm t) => Closed (Definition t) -> Closed (Type t)
definitionType (Constant _ type_)   = type_
definitionType (DataCon _ tel)      = telPi tel
definitionType (Projection _ _ tel) = telPi tel
definitionType (Function type_ _)   = type_

isRecordType :: (IsTerm t) => Sig.Signature t -> Name -> Bool
isRecordType sig tyCon =
  case Sig.getDefinition sig tyCon of
    Constant (Record _ _) _ -> True
    _                       -> False

isRecordConstr :: (IsTerm t) => Sig.Signature t -> Name -> Bool
isRecordConstr sig dataCon =
  case Sig.getDefinition sig dataCon of
    DataCon tyCon _ -> isRecordType sig tyCon
    _               -> False

-- | Check whether a term @Def f es@ could be reduced, if its arguments
-- were different.
isNeutral :: (IsTerm t) => Sig.Signature t -> Name -> Bool
isNeutral sig f =
  case Sig.getDefinition sig f of
    Constant{}    -> False
    DataCon{}     -> error $ "impossible.Check.isNeutral: constructor " ++ show f
    Projection{}  -> error $ "impossible.Check.isNeutral: projection " ++ show f
    Function{}    -> True
    -- TODO: more precise analysis
    -- We need to check whether a function is stuck on a variable
    -- (not meta variable), but the API does not help us...

-- Whnf'ing and view'ing
------------------------

whnfTC :: (IsVar v, IsTerm t) => t v -> TC t v' (Blocked t v)
whnfTC t = do
  sig <- getSignature
  return $ whnf sig t

whnfViewTC :: (IsVar v, IsTerm t) => t v -> TC t v' (TermView t v)
whnfViewTC t = view . ignoreBlocking <$> whnfTC t

nfTC :: (IsVar v, IsTerm t) => t v -> TC t v' (t v)
nfTC t = do
  sig <- getSignature
  return $ nf sig t

-- Matching terms
-----------------

-- TODO remove duplication

matchTyCon
  :: (IsVar v, IsTerm t, Typeable a)
  => Name
  -> Type t v
  -> CheckError t v             -- ^ Error
  -> ([Term t v] -> StuckTC t v a)
  -> StuckTC t v a
matchTyCon tyCon t err handler = do
  blockedT <- whnfTC t
  let t' = ignoreBlocking blockedT
  case blockedT of
    NotBlocked _
      | App (Def tyCon') tyConArgs0 <- view t'
      , tyCon == tyCon', Just tyConArgs <- mapM isApply tyConArgs0 -> do
        handler tyConArgs
    MetaVarHead mv _ -> do
      liftClosed $ do
        mvType <- getTypeOfMetaVar mv
        mvT <- unrollPiTC mvType $ \ctxMvArgs _ -> do
          Constant _ tyConType <- getDefinition tyCon
          tyConParsTel <- unrollPiTC (vacuous tyConType) $ \ctx ->
                          return . Tel.idTel ctx
          tyConPars <- createMvsPars tyConParsTel
          return $ ctxLam ctxMvArgs $ def tyCon $ map Apply tyConPars
        instantiateMetaVar mv mvT
      -- TODO Dangerous recursion, relying on correct instantiation.
      -- Maybe remove and do it explicitly?
      matchTyCon tyCon t' err handler
    BlockedOn mvs _ _ -> do
      fmap StuckOn $ newProblem mvs (MatchTyCon tyCon t') $ do
        matchTyCon tyCon t' err handler
    _ -> do
      NotStuck <$> checkError err

createMvsPars :: (IsVar v, IsTerm t) => Tel.IdTel (Type t) v -> TC t v [Term t v]
createMvsPars (Tel.Empty _) =
  return []
createMvsPars (Tel.Cons (_, type') tel) = do
  mv  <- addMetaVarInCtx type'
  mvs <- createMvsPars (Tel.instantiate tel mv)
  return (mv : mvs)

matchPi
  :: (IsVar v, IsTerm t, Typeable a)
  => Name                       -- ^ Name for the bound var in the codomain.
  -> Type t v
  -> CheckError t v             -- ^ Error
  -> (Type t v -> Abs (Type t) v -> StuckTC t v a)
  -> StuckTC t v a
matchPi name t err handler = do
  blockedT <- whnfTC t
  let t' = ignoreBlocking blockedT
  case blockedT of
    NotBlocked _ | Pi dom cod <- view t' -> do
      handler dom cod
    MetaVarHead mv _ -> do
      liftClosed $ do
        mvType <- getTypeOfMetaVar mv
        mvT <- unrollPiTC mvType $ \ctxMvArgs _ -> do
          dom <- addMetaVarInCtx set
          cod <- extendContext name dom $ \_ -> addMetaVarInCtx set
          return $ ctxLam ctxMvArgs $ pi dom $ toAbs cod
        instantiateMetaVar mv mvT
      -- TODO Dangerous recursion, relying on correct instantiation.
      -- Maybe remove and do it explicitly?
      matchPi name t' err handler
    BlockedOn mvs _ _ -> do
      fmap StuckOn $ newProblem mvs (MatchPi t') $ do
        matchPi name t' err handler
    _ -> do
      NotStuck <$> checkError err

matchPi_
  :: (IsVar v, IsTerm t, Typeable a)
  => Type t v
  -> CheckError t v             -- ^ Error
  -> (Type t v -> Abs (Type t) v -> StuckTC t v a)
  -> StuckTC t v a
matchPi_ = matchPi "_"

matchEqual
  :: (IsVar v, IsTerm t, Typeable a)
  => Type t v
  -> CheckError t v             -- ^ Error
  -> (Type t v -> Term t v -> Term t v -> StuckTC t v a)
  -> StuckTC t v a
matchEqual t err handler = do
  blockedT <- whnfTC t
  let t' = ignoreBlocking blockedT
  case blockedT of
    NotBlocked _ | Equal type_ t1 t2 <- view t' -> do
      handler type_ t1 t2
    MetaVarHead mv _ -> do
      liftClosed $ do
        mvType <- getTypeOfMetaVar mv
        mvT <- unrollPiTC mvType $ \ctxMvArgs _ -> do
          type_ <- addMetaVarInCtx set
          t1 <- addMetaVarInCtx type_
          t2 <- addMetaVarInCtx type_
          return $ ctxLam ctxMvArgs $ equal type_ t1 t2
        instantiateMetaVar mv mvT
      matchEqual t' err handler
    BlockedOn mvs _ _ ->
      fmap StuckOn $ newProblem mvs (MatchEqual t') $ do
        matchEqual t' err handler
    _ -> do
      NotStuck <$> checkError err

instantiateDataCon
  :: (IsTerm t)
  => MetaVar
  -> Name
  -- ^ Name of the datacon
  -> ClosedTC t (Closed (Term t))
instantiateDataCon mv dataCon = do
  mvType <- getTypeOfMetaVar mv
  mvT <- unrollPiTC mvType $ \ctxMvArgs endType' -> do
    DataCon tyCon dataConTypeTel <- getDefinition dataCon
    -- We know that the metavariable must have the right type (we have
    -- typechecked the arguments already).
    App (Def tyCon') tyConArgs0 <- whnfViewTC endType'
    Just tyConArgs <- return $ mapM isApply tyConArgs0
    True <- return $ tyCon == tyCon'
    let dataConType = Tel.substs (vacuous dataConTypeTel) tyConArgs
    dataConArgsTel <- unrollPiTC dataConType $ \ctx -> return . Tel.idTel ctx
    dataConArgs <- createMvsPars dataConArgsTel
    return $ ctxLam ctxMvArgs $ con dataCon $ dataConArgs
  instantiateMetaVar mv mvT
  return mvT

-- Problems shortcuts
---------------------

newProblemCheckEqual
    :: (IsTerm t, IsVar v, Typeable v, Typeable t)
    => Set.Set MetaVar -> Type t v -> Term t v -> Term t v
    -> TC t v (ProblemId ())
newProblemCheckEqual mvs type_ x y = do
    newProblem mvs (CheckEqual type_ x y) $ checkEqual type_ x y

bindProblemCheckEqual
    :: (IsTerm t, IsVar v, Typeable a, Typeable v, Typeable t)
    => ProblemId a -> Type t v -> Term t v -> Term t v -> TC t v (ProblemId ())
bindProblemCheckEqual pid type_ x y = do
    bindProblem pid (CheckEqual type_ x y) $ \_ -> checkEqual type_ x y

-- Errors
------------------------------------------------------------------------

data CheckError t v
    = DataConTypeError A.Expr (Type t v)
    | LambdaTypeError A.Expr (Type t v)
    | NotEqualityType (Type t v)
    | ExpectedFunctionType (Type t v) (Maybe A.Expr)
    | CannotInferTypeOf A.Expr
    | TermsNotEqual (Term t v) (Term t v)
    | SpineNotEqual (Type t v) [Elim t v] [Elim t v]
    | ExpectingRecordType (Type t v)
    | FreeVariableInEquatedTerm MetaVar [Elim t v] (Term t v) v
    | PatternMatchOnRecord A.Pattern
                           Name -- Record type constructor
    | MismatchingPattern (Type t v) A.Pattern
    | OccursCheckFailed MetaVar (Term t v)
    | NameNotInScope Name
    | StuckTypeSignature Name
    | ClausesAlreadyAdded Name

checkError :: (IsVar v, IsTerm t) => CheckError t v -> TC t v a
checkError err = do
    sig <- getSignature
    typeError $ renderError sig err

renderError :: (IsVar v, IsTerm t) => Sig.Signature t -> CheckError t v -> String
renderError sig term0 = case term0 of
  DataConTypeError synT type_ ->
    "DataCon type error " ++ render synT ++ " : " ++ renderTerm type_
  NotEqualityType type_ ->
    "Expecting an equality type: " ++ renderTerm type_
  LambdaTypeError synT type_ ->
    "Lambda type error\n" ++ render synT ++ "\n  :\n" ++ renderTerm type_
  ExpectedFunctionType type_ mbArg ->
    "Expected function type " ++ renderTerm type_ ++
    (case mbArg of
       Nothing  -> ""
       Just arg -> "\nIn application of " ++ render arg)
  CannotInferTypeOf synT ->
    "Cannot infer type of " ++ render synT
  TermsNotEqual t1 t2 ->
    renderTerm t1 ++ "\n  !=\n" ++ renderTerm t2
  SpineNotEqual type_ es1 es2 ->
    render es1 ++ "\n  !=\n" ++ render es2 ++ "\n  :\n" ++ renderTerm type_
  ExpectingRecordType type_ ->
    "Expecting record type: " ++ renderTerm type_
  FreeVariableInEquatedTerm mv els rhs v ->
    "Free variable `" ++ renderVar v ++ "' in term equated to metavariable application:\n" ++
    renderTerm (metaVar mv els) ++ "\n" ++
    "  =\n" ++
    renderTerm rhs
  PatternMatchOnRecord synPat tyCon ->
    "Cannot have pattern " ++ render synPat ++ " for record type " ++ render tyCon
  MismatchingPattern type_ synPat ->
    render synPat ++ " does not match an element of type " ++ renderTerm type_
  OccursCheckFailed mv t ->
    "Attempt at recursive instantiation: " ++ render mv ++ " := " ++ renderTerm t
  NameNotInScope name ->
    "Name not in scope: " ++ render name
  StuckTypeSignature name ->
    "Got stuck on the type signature when checking clauses for function " ++ render name
  ClausesAlreadyAdded fun ->
    "Clauses already added for function " ++ render fun
  where
    renderVar = render . varName
    renderTerm = render . prettyTerm sig

prettyTerm :: (IsVar v, IsTerm t) => Sig.Signature t -> t v -> PP.Doc
prettyTerm sig = PP.pretty . view . instantiateMetaVars sig

instantiateMetaVars :: (IsVar v, IsTerm t) => Sig.Signature t -> t v -> t v
instantiateMetaVars sig t = unview $
  case view t of
    Lam abs ->
      Lam (goAbs abs)
    Pi dom cod ->
      Pi (go dom) (goAbs cod)
    Equal type_ x y ->
      Equal (go type_) (go x) (go y)
    Refl ->
      Refl
    Con dataCon ts ->
      Con dataCon $ map go ts
    Set ->
      Set
    App (Meta mv) els | Just t' <- Sig.getMetaVarBody sig mv ->
      view $ instantiateMetaVars sig $ eliminate (vacuousM t') els
    App h els ->
      App h $ map goElim els
  where
    go = instantiateMetaVars sig

    goAbs = toAbs . instantiateMetaVars sig . fromAbs

    goElim (Proj n field) = Proj n field
    goElim (Apply t')     = Apply (go t')

-- Non-monadic stuff
------------------------------------------------------------------------

isApply :: Elim (Term t) v -> Maybe (Term t v)
isApply (Apply v) = Just v
isApply Proj{}    = Nothing

-- Telescope & context utils
----------------------------

telPi :: (IsVar v, IsTerm t) => Tel.IdTel (Type t) v -> Type t v
telPi tel = Tel.unTel tel $ \ctx endType -> ctxPi ctx (Tel.unId endType)

-- | Collects all the variables in the 'Ctx.Ctx'.
ctxVars :: IsTerm t => Ctx.Ctx v0 (Type t) v -> [v]
ctxVars = reverse . go
  where
    go :: IsTerm t => Ctx.Ctx v0 (Type t) v -> [v]
    go Ctx.Empty                = []
    go (Ctx.Snoc ctx (name, _)) = boundTermVar name : map F (go ctx)

-- | Applies a 'Term' to all the variables in the context.  The
-- variables are applied from left to right.
ctxApp :: (IsVar v, IsTerm t) => Term t v -> Ctx.Ctx v0 (Type t) v -> Term t v
ctxApp t ctx0 = eliminate t $ map (Apply . var) $ ctxVars ctx0

-- | Creates a 'Pi' type containing all the types in the 'Ctx' and
-- terminating with the provided 't'.
ctxPi :: IsTerm t => Ctx.Ctx v0 (Type t) v -> Type t v -> Type t v0
ctxPi Ctx.Empty                  t = t
ctxPi (Ctx.Snoc ctx (_n, type_)) t = ctxPi ctx $ pi type_ (toAbs t)

-- | Creates a 'Lam' term with as many arguments there are in the
-- 'Ctx.Ctx'.
ctxLam :: IsTerm t => Ctx.Ctx v0 (Type t) v -> Term t v -> Term t v0
ctxLam Ctx.Empty        t = t
ctxLam (Ctx.Snoc ctx _) t = ctxLam ctx $ lam $ toAbs t

-- Types of problems
------------------------------------------------------------------------

data CheckProblem t v
    = CheckEqual (Type t v) (Term t v) (Term t v)
    | WaitForInfer A.Expr (Type t v)
    | MetaVarIfStuck (Term t v) (Type t v) (ProblemId (Term t v))
    | forall a. WaitingOn (ProblemId a)
    | CheckSpine (Term t v) [A.Elim] (Type t v)
    | EqualSpine (Term t v) [Elim t v] [Elim t v] (Type t v)
    | MatchTyCon Name (Type t v)
    | MatchPi (Type t v)
    | MatchEqual (Type t v)

instance Nf CheckProblem where
  nf' sig desc = case desc of
    CheckEqual type_ x y -> CheckEqual (nf sig type_) (nf sig x) (nf sig y)
    WaitForInfer synT type_ -> WaitForInfer synT (nf sig type_)
    MetaVarIfStuck mv type_ pid -> MetaVarIfStuck (nf sig mv) (nf sig type_) pid
    WaitingOn pid -> WaitingOn pid
    CheckSpine t elims type_ -> CheckSpine (nf sig t) elims (nf sig type_)
    EqualSpine t elims1 elims2 type_ -> EqualSpine (nf sig t) (map (nf' sig) elims1) (map (nf' sig) elims2) (nf sig type_)
    MatchTyCon tyCon type_ -> MatchTyCon tyCon (nf sig type_)
    MatchPi type_ -> MatchPi (nf sig type_)
    MatchEqual type_ -> MatchEqual (nf sig type_)

instance (IsVar v, IsTerm t) => PP.Pretty (CheckProblem t v)  where
    pretty desc = case desc of
      CheckEqual type_ x y ->
        prettyView x $$ PP.nest 2 "=" $$ prettyView y $$
        PP.nest 2 ":" $$
        prettyView type_
      WaitForInfer synT type_ ->
        "Waiting for inference of" $$ PP.nest 2 (
          PP.pretty synT $$ PP.nest 2 ":" $$ prettyView type_)
      MetaVarIfStuck mvT type_ pid | App (Meta mv) _ <- view mvT ->
        "Waiting to equate placeholder" <+> PP.pretty mv <+> "of type" $$
        PP.nest 2 (prettyView type_) $$
        "to result of problem" <+> PP.text (show pid)
      MetaVarIfStuck mvT _ _ ->
        error $ "PP.Pretty CheckProblem: got non-meta term: " ++ renderView mvT
      WaitingOn pid ->
        "Waiting on" <+> PP.text (show pid)
      CheckSpine t elims type_ ->
        "Checking spine" $$ PP.nest 2 (
          PP.prettyApp 0 (prettyView t) elims $$ PP.nest 2 ":" $$ prettyView type_)
      EqualSpine h elims1 elims2 type_ ->
        "Equating spine" $$ PP.nest 2 (prettyView h) $$ PP.nest 2 (
          PP.pretty elims1 $$ PP.nest 2 "=" $$ PP.pretty elims2 $$
          PP.nest 2 ":" $$
          prettyView type_)
      MatchTyCon name type_ ->
        ("Matching tycon" <+> PP.pretty name <+> "with type") $$ prettyView type_
      MatchPi type_ ->
        "Matching pi type" $$ prettyView type_
      MatchEqual type_ ->
        "Matching equal" $$ prettyView type_

-- Constants
------------------------------------------------------------------------

-- (A : Set) ->
-- (x : A) ->
-- (y : A) ->
-- (P : (x : A) -> (y : A) -> (eq : _==_ A x y) -> Set) ->
-- (p : (x : A) -> P x x refl) ->
-- (eq : _==_ A x y) ->
-- P x y eq
typeOfJ :: forall t. (IsTerm t) => Closed (Type t)
typeOfJ = fmap close $
    ("A", set) -->
    ("x", var "A") -->
    ("y", var "A") -->
    ("P", ("x", var "A") --> ("y", var "A") -->
          ("eq", equal (var "A") (var "x") (var "y")) -->
          set
    ) -->
    ("p", ("x", var "A") --> app (Var "P") (map Apply [var "x", var "x", refl])) -->
    ("eq", equal (var "A") (var "x") (var "y")) -->
    app (Var "P") (map Apply [var "x", var "y", refl])
  where
    close :: Name -> Void
    close v = error $ "impossible.typeOfJ: Free variable " ++ render v

    infixr 9 -->
    (-->) :: (Name, t Name) -> t Name -> t Name
    (x, type_) --> t = pi type_ $ abstract x t
