{-# LANGUAGE OverloadedStrings #-}
module TypeCheck3.Solve.Common where

import           Prelude                          hiding (any)

import           Control.Monad.Trans.Maybe        (MaybeT(MaybeT), runMaybeT)
import qualified Data.HashSet                     as HS
import qualified Data.Set                         as Set
import           Syntax.Internal                  (Name)

import           Prelude.Extended
import           PrettyPrint                      (($$), (<+>), (//>), (//), group, hang)
import qualified PrettyPrint                      as PP
import           Term
import           Term.Context                     (Ctx)
import qualified Term.Context                     as Ctx
import qualified Term.Signature                   as Sig
import qualified Term.Telescope                   as Tel
import           TypeCheck3.Common
import qualified TypeCheck3.Core                  as Core
import           TypeCheck3.Monad

-- Unification stuff which is common amongst the solvers.
------------------------------------------------------------------------

-- | The term must be in normal form.
--
-- Returns the pruned term.
pruneTerm
    :: (IsTerm t)
    => Set.Set Var                -- ^ allowed vars
    -> Term t
    -> TC t s (Term t)
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
    :: forall t s.
       (IsTerm t)
    => Set.Set Var           -- ^ allowed vars
    -> MetaVar
    -> [Elim (Term t)]       -- ^ Arguments to the metavariable
    -> TC t s (Maybe (Closed (Term t)))
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
        lift $ instantiateMetaVar oldMv mvT
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
      :: Type t -> [Bool] -> TC t s (Tel.Tel (Type t), Type t, [Named Bool])
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
          fatalError "impossible.createNewMeta: metavar type too short"
prune _ _ _ = do
  -- TODO we could probably do something more.
  return Nothing

-- | Returns whether the term should be killed, given a set of allowed
-- variables.
shouldKill
  :: (IsTerm t)
  => Set.Set Var -> Term t -> TC t s (Maybe Bool)
shouldKill vs t = runMaybeT $ do
  tView <- lift $ whnfViewTC t
  case tView of
    Lam _ ->
      mzero
    Con dataCon args -> do
      guard =<< lift (isRecordConstr dataCon)
      and <$> mapM (MaybeT . shouldKill vs) args
    App (Def f) _ -> do
      neutr <- not <$> lift (isNeutral f =<< withSignature id)
      if neutr then mzero else fallback
    _ ->
      fallback
  where
    fallback = lift $ withSignatureTermM $ \sig -> do
      fvs <- freeVars sig t
      return $ not (fvRigid fvs `Set.isSubsetOf` vs)

    -- | Check whether a term @Def f es@ could be reduced, if its arguments
    -- were different.
    isNeutral f sig =
      case Sig.getDefinition sig f of
        Constant{}    -> return False
        DataCon{}     -> fatalError $ "impossible.isNeutral: constructor " ++ show f
        Projection{}  -> fatalError $ "impossible.isNeutral: projection " ++ show f
        Function{}    -> return True
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
  :: (IsTerm t) => InvertMeta t -> TC t s PP.Doc
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
  :: forall t s.
     (IsTerm t)
  => [Elim (Term t)]
  -> TC t s (TermTraverse () (InvertMeta t))
invertMeta elims0 = case mapM isApply elims0 of
    -- First we build up a list of variables representing the bound
    -- arguments in the metavar body.
    Just args0 -> go args0 $ reverse [V (Named "_" ix) | (ix, _) <- zip [0..] args0]
    Nothing    -> return $ TTFail ()
  where
    -- Then we try to invert passing pairs of arguments to the
    -- metavariable and bound arguments of the body of the
    -- metavariable.
    go :: [Term t] -> [Var] -> TC t s (TermTraverse () (InvertMeta t))
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
    checkArgs :: [(Term t, Term t)] -> TC t s (TermTraverse () [(Var, Term t)])
    checkArgs xs = do
      res <- mapM (uncurry checkArg) xs
      return $ concat <$> sequenceA res

    checkArg
      :: Term t
      -- ^ Term outside (argument to the metavar)
      -> Term t
      -- ^ Term inside (corresponding bound variable)
      -> TC t s (TermTraverse () [(Var, Term t)])
    checkArg arg v = do
      blockedArg <- whnfTC arg
      case blockedArg of
        -- If the argument is a variable, we are simply going to replace
        -- it with the corresponding variable in the body of the meta.
        NotBlocked t -> do
          tView <- whnfViewTC t
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
  :: forall t s.
     (IsTerm t)
  => InvertMeta t -> Term t
  -> TC t s (TermTraverse Var (Closed (Term t)))
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
lambdaAbstract :: (IsTerm t) => Int -> Term t -> TC t s (Term t)
lambdaAbstract n t | n <= 0 = return t
lambdaAbstract n t = (lamTC <=< lambdaAbstract (n - 1)) t

applyInvertMetaSubst
  :: forall t s.
     (IsTerm t)
  => [(Var, Term t)]
  -- ^ Inversion from variables outside to terms inside
  -> Term t
  -- ^ Term outside
  -> TC t s (TermTraverse Var (Term t))
  -- ^ Either we fail with a variable that isn't present in the
  -- substitution, or we return a new term.
applyInvertMetaSubst sub t0 =
  flip go t0 $ \v -> return $ maybe (Left v) Right (lookup v sub)
  where
    lift' :: (Var -> TC t s (Either Var (Term t)))
          -> (Var -> TC t s (Either Var (Term t)))
    lift' f v0 = case strengthenVar_ 1 v0 of
      Nothing ->
        Right <$> varTC v0
      Just v -> do
        e <- f v
        case e of
          Left v' -> return $ Left v'
          Right t -> Right <$> (liftTermM (weaken_ 1 t))

    go :: (Var -> TC t s (Either Var (Term t))) -> Term t -> TC t s (TermTraverse Var t)
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

isProjectedVar :: (IsTerm t) => Elim t -> MaybeT (TC t s) (Var, Name)
isProjectedVar elim = do
  Apply t <- return elim
  App (Var v) vElims <- lift $ whnfViewTC t
  projName : _ <- forM vElims $ \vElim -> do
    Proj projName _ <- return vElim
    return projName
  return (v, projName)

-- | Scans a list of 'Elim's looking for an 'Elim' composed of projected
-- variable.
collectProjectedVar
  :: (IsTerm t) => [Elim t] -> TC t s (Maybe (Var, Name))
collectProjectedVar elims = runMaybeT $ do
  (v, projName) <- msum $ map isProjectedVar elims
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

etaContractElim :: (IsTerm t) => Elim t -> TC t s (Elim t)
etaContractElim (Apply t)  = Apply <$> etaContract t
etaContractElim (Proj n f) = return $ Proj n f

etaContract :: (IsTerm t) => t -> TC t s t
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

killArgs :: (IsTerm t) => MetaVar -> [Named Bool] -> TC t s (Closed (Term t))
killArgs newMv kills = do
  let vs = reverse [ V (Named n ix)
                   | (ix, Named n kill) <- zip [0..] (reverse kills), not kill
                   ]
  body <- metaVarTC newMv . map Apply =<< mapM varTC vs
  foldl' (\body' _ -> lamTC =<< body') (return body) kills

-- Non-metas stuff
------------------------------------------------------------------------

-- | @intersectVars us vs@ checks whether all relevant elements in @us@
--   and @vs@ are variables, and if yes, returns a prune list which says
--   @True@ for arguments which are different and can be pruned.
intersectVars :: (IsTerm t) => [Elim t] -> [Elim t] -> TC t s (Maybe [Named Bool])
intersectVars els1 els2 = runMaybeT $ mapM (uncurry areVars) $ zip els1 els2
  where
    areVars (Apply t1) (Apply t2) = do
      t1View <- lift $ whnfViewTC t1
      t2View <- lift $ whnfViewTC t2
      case (t1View, t2View) of
        (App (Var v1) [], App (Var v2) []) -> return $ (v1 /= v2) <$ unVar v1 -- prune different vars
        (_,               _)               -> mzero
    areVars _ _ =
      mzero

instantiateDataCon
  :: (IsTerm t)
  => MetaVar
  -> Name
  -- ^ Name of the datacon
  -> TC t s (Closed (Term t))
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
  -- given the usage, here we know that the body is going to be well typed.
  -- TODO make sure that the above holds.
  instantiateMetaVar mv mvT
  return mvT

createMvsPars
  :: (IsTerm t) => Ctx t -> Tel.Tel (Type t) -> TC t s [Term t]
createMvsPars _ Tel.Empty =
  return []
createMvsPars ctx (Tel.Cons (_, type') tel) = do
  mv  <- addMetaVarInCtx ctx type'
  mvs <- createMvsPars ctx =<< liftTermM (Tel.instantiate tel mv)
  return (mv : mvs)

applyProjection
  :: (IsTerm t)
  => Name
  -- ^ Name of the projection
  -> Term t
  -- ^ Head
  -> Type t
  -- ^ Type of the head
  -> TC t s (Term t, Type t)
applyProjection proj h type_ = do
  Projection projIx tyCon projTypeTel projType <- getDefinition proj
  h' <- eliminateTC h [Proj proj projIx]
  App (Def tyCon') tyConArgs0 <- whnfViewTC type_
  let _assert@True = tyCon == tyCon'
  let Just tyConArgs = mapM isApply tyConArgs0
  appliedProjType <- liftTermM $ Tel.substs projTypeTel projType tyConArgs
  Pi _ endType <- whnfViewTC appliedProjType
  endType' <- instantiateTC endType h
  return (h', endType')
