{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Unify.Common where

import qualified Prelude
import qualified Data.HashSet                     as HS
import qualified Data.Set                         as Set
import           Data.Tree                        (Tree(Node), subForest, rootLabel, Forest)

import           Instrumentation
import           Names
import           TogPrelude
import           PrettyPrint                      (($$), (<+>), (//>))
import qualified PrettyPrint                      as PP
import           Term
import           Monad
import           TypeCheck
import           Data.Collect

#include "impossible.h"

-- Pruning
------------------------------------------------------------------------

{-# WARNING curryMeta "Remove this, do the unrolling on-demand in prune." #-}
-- | @curryMeta t@ checks if @t = α ts@ and for every argument
-- of the metavar which is a record type it splits it up in separate
-- arguments, one for each field.
curryMeta
  :: forall t r s. (IsTerm t) => Term t -> TC t r s (Term t)
curryMeta t = do
  let msg = do
        tDoc <- prettyM t
        return $
          "term:" //> tDoc
  debugBracket "curryMeta" msg $ fmap (fromMaybe t) $ runMaybeT $ do
    App (Meta mv) _ <- lift $ whnfView t
    (tel, mvType) <- lift $ unrollPi =<< getMetaType mv
    (True, args0, newMvType) <- lift $ go tel mvType
    lift $ do
      let abstractions = length args0
      args <- toArgs args0
      newMv <- addMeta newMvType
      mvT <- meta newMv $ map Apply args
      let mi = MetaBody abstractions mvT
      debug "unrolled" $ do
        mvTypeDoc <- prettyM =<< telPi tel mvType
        newMvTypeDoc <- prettyM newMvType
        mvTDoc <- prettyM mi
        return $
          "old type:" //> mvTypeDoc $$
          "new type:" //> newMvTypeDoc $$
          "term:" //> mvTDoc
      instantiateMeta mv mi
      -- Now we return the old type, which normalized will give the new
      -- mv.
      return t
  where
    treePaths :: Tree a -> [[a]]
    treePaths tr | null (subForest tr) = [[rootLabel tr]]
    treePaths tr = concatMap (map (rootLabel tr :) . treePaths)  (subForest tr)

    toArgs :: MetaArgs t -> TC t r s [Term t]
    toArgs args = fmap concat $ forM args $ \mbArg -> do
      case mbArg of
        Nothing -> do
          return []
        Just (v, projs) -> do
          let projsPaths = concatMap treePaths projs
          if null projsPaths
            then do
              t' <- app (Var v) []
              return [t']
            else do
              mapM (app (Var v) . map Proj) projsPaths

    go :: Tel t -> Type t -> TC t r s (Bool, MetaArgs t, Type t)
    go T0 type_ = do
      return (False, [], type_)
    go ((n, dom) :> tel) type0 = do
      let fallback = do
            (changed, args, type1) <- go tel type0
            let argVar = weakenVar_ (length args) $ boundVar n
            type2 <- pi dom type1
            return (changed, Just (argVar, []) : args, type2)
      domView <- whnfView dom
      case domView of
        App (Def tyCon) elims -> do
          tyConDef <- getDefinition tyCon
          case tyConDef of
            Constant _ (Record dataCon projs) -> do
              let Just tyConPars = mapM isApply elims
              DataCon _ _ dataConType <- getDefinition dataCon
              appliedDataConType <- openContextual dataConType tyConPars
              debug_ "tyConPars" $ PP.text $ show $ show tyConPars
              (dataConPars0, _) <-
                assert_ ("curryMeta, unrollPiWithNames:" <+>) $
                unrollPiWithNames appliedDataConType (map (qNameName . pName . opndKey) projs)
              let dataConPars = telToCtx dataConPars0
              let numDataConPars = ctxLength dataConPars
              recordTerm <- con dataCon =<< mapM var (ctxVars dataConPars)
              let telLen = telLength tel
              let weakenBy = numDataConPars
              if weakenBy <= 0
                -- This means that the type was unit.
                then do
                  tel' <- instantiate_ tel recordTerm
                  type1 <- applySubst type0 . subLift telLen =<< subSingleton recordTerm
                  (_, args, type2) <- go (dataConPars `telAppend` tel') type1
                  return (True, Nothing : args, type2)
                else do
                  sub <- subInstantiate recordTerm $ subWeaken numDataConPars subId
                  tel' <- applySubst tel sub
                  type1 <- applySubst type0 $ subLift telLen sub
                  (_, args, type2) <- go (dataConPars `telAppend` tel') type1
                  let (argsL, argsR) = strictSplitAt (length projs) args
                  let argVar = weakenVar_ (length argsR) $ boundVar n
                  let argL = ( argVar
                             , [ Node proj projs'
                               | (proj, Just (_, projs')) <- zip projs argsL
                               ]
                             )
                  return (True, Just argL : argsR, type2)
            _ -> do
              fallback
        _ -> do
          fallback

-- | @pruneTerm vs t@ tries to remove all the variables that are not
--   in @vs@ by instantiating metavariables that can make such
--   variables disappear.  Always succeeds, but might not eliminate
--   all the variables.
pruneTerm
    :: (IsTerm t)
    => Set.Set Var                -- ^ allowed vars
    -> Term t
    -> TC t r s (Term t)
pruneTerm vs t = do
  let msg = do
        tDoc <- prettyM t
        return $
          "allowed vars:" <+> PP.pretty (Set.toList vs) $$
          "term:" //> tDoc
  debugBracket "pruneTerm" msg $ pruneTerm' vs t

pruneTerm'
    :: (IsTerm t)
    => Set.Set Var                -- ^ allowed vars
    -> Term t
    -> TC t r s (Term t)
pruneTerm' vs t = do
  tView <- whnfView t
  case tView of
    Lam body -> do
      name <- getAbsName_ body
      lam =<< pruneTerm' (addVar name) body
    Pi domain codomain -> do
      name <- getAbsName_ codomain
      join $ pi <$> pruneTerm' vs domain <*> pruneTerm' (addVar name) codomain
    Equal type_ x y -> do
      join $ equal <$> pruneTerm' vs type_ <*> pruneTerm' vs x <*> pruneTerm' vs y
    App (Meta mv) elims -> do
      -- First try to curry and expand
      mvT <- meta mv elims
      -- TODO do expansion/currying more lazily, and optimize by first
      -- checking if we need to do anything at all.
      mvTView <- whnfView =<< etaExpandMeta =<< curryMeta mvT
      case mvTView of
        App (Meta mv') elims' -> do
          mbMvT' <- prune vs mv' elims'
          case mbMvT' of
            Nothing   -> return mvT
            Just mvT' -> eliminate mvT' elims'
        _ -> do
          pruneTerm' vs mvT
    App h elims -> do
      app h =<< mapM pruneElim elims
    Set ->
      return set
    Refl ->
      return refl
    Con dataCon args ->
      con dataCon =<< mapM (pruneTerm' vs) args
  where
    pruneElim (Apply t') = Apply <$> pruneTerm' vs t'
    pruneElim (Proj p)   = return $ Proj p

    addVar name = Set.insert (boundVar name) (Set.mapMonotonic (weakenVar_ 1) vs)

type MetaArgs t = [Maybe (Var, Forest (Opened Projection t))]

-- | @prune vs α es@ tries to prune all the variables in @es@ that are
--   not in @vs@, by instantiating @α@.  If we managed to prune
--   anything returns 'Just', 'Nothing' if we can't prune or no prune
--   is needed.
prune
    :: forall t r s.
       (IsTerm t)
    => Set.Set Var           -- ^ allowed vars
    -> Meta
    -> [Elim (Term t)]       -- ^ Arguments to the metavariable
    -> TC t r s (Maybe (Closed (Term t)))
prune allowedVs oldMv elims = do
  -- TODO can we do something more if we have projections?
  runMaybeT $ do
    args <- MaybeT $ return $ mapM isApply elims
    kills0 <- MaybeT $ sequence <$> mapM (shouldKill allowedVs) args
    guard (or kills0)
    let msg = do
          mvTypeDoc <- prettyM =<< getMetaType oldMv
          elimsDoc <- prettyM elims
          return $
            "metavar type:" //> mvTypeDoc $$
            "metavar:" <+> PP.pretty oldMv $$
            "elims:" //> elimsDoc $$
            "to kill:" //> PP.pretty kills0 $$
            "allowed vars:" //> PP.pretty (Set.toList allowedVs)
    MaybeT $ debugBracket "prune" msg $ runMaybeT $ do
      oldMvType <- lift $ getMetaType oldMv
      (newMvType, kills1) <- lift $ createNewMeta oldMvType kills0
      lift $ debug_ "new kills" $ PP.pretty (map unNamed kills1)
      guard (any unNamed kills1)
      newMv <- lift $ addMeta newMvType
      mi <- lift $ killArgs newMv kills1
      lift $ instantiateMeta oldMv mi
      lift $ metaBodyToTerm mi
  where
    -- We build a pi-type with the non-killed types in.  This way, we
    -- can analyze the dependency between arguments and avoid killing
    -- things that later arguments depend on.
    --
    -- At the end of the type we put both the new metavariable and the
    -- remaining type, so that this dependency check will be performed
    -- on it as well.
    createNewMeta
      :: Type t -> [Bool] -> TC t r s (Type t, [Named Bool])
    createNewMeta type_ [] =
      return (type_, [])
    createNewMeta type_ (kill : kills) = do
      typeView <- whnfView type_
      case typeView of
        Pi domain codomain -> do
          name <- getAbsName_ codomain
          (type', kills') <- createNewMeta codomain kills
          debug "createNewMeta" $ do
            domDoc <- prettyM domain
            typeDoc <- prettyM type'
            return $
              "kill:" <+> PP.pretty kill $$
              "type:" //> domDoc $$
              "strengthening:" //> typeDoc
          let notKilled = do
                type'' <- pi domain type'
                return (type'', named name False : kills')
          if not kill
            then notKilled
            else do
              mbType <- safeStrengthen =<< nf type'
              case mbType of
                Just type'' -> do return (type'', named name True : kills')
                Nothing     -> do debug_ "couldn't strengthen" ""
                                  notKilled
        _ ->
          fatalError "impossible.createNewMeta: metavar type too short"

-- | Returns whether the term should be killed, given a set of allowed
--   variables.
shouldKill
  :: (IsTerm t)
  => Set.Set Var -> Term t -> TC t r s (Maybe Bool)
shouldKill vs t = runMaybeT $ do
  tView <- lift $ whnfView t
  case tView of
    Lam _ ->
      mzero
    Con dataCon args -> do
      guard =<< lift (isRecordConstr dataCon)
      or <$> mapM (MaybeT . shouldKill vs) args
    App (Def f) _ -> do
      neutr <- not <$> lift (isNeutral f)
      if neutr then mzero else fallback
    _ ->
      fallback
  where
    fallback = lift $ do
      fvs <- freeVars t
      return $ not (fvRigid fvs `Set.isSubsetOf` vs)

    -- | Check whether a term @Def f es@ could be reduced, if its arguments
    -- were different.
    isNeutral f = do
      def' <- getDefinition f
      case def' of
        Constant _ Function{} -> return True
        Constant{}            -> return False
        _                     -> __IMPOSSIBLE__
        -- TODO: more precise analysis
        -- We need to check whether a function is stuck on a variable
        -- (not meta variable), but the API does not help us...

-- Tools useful for expanding of contexts.
------------------------------------------------------------------------

-- | Checks whether an eliminator is a a projected variables (because
--   we can expand those).
--
--   Returns the variable and the projection name.
isProjectedVar :: (IsTerm t) => Elim t -> MaybeT (TC t r s) (Var, Opened QName t)
isProjectedVar elim = do
  Apply t <- return elim
  App (Var v) vElims <- lift $ whnfView t
  Proj p : _ <- lift $ return vElims
  return (v, first pName p)

-- | @etaExpandContextVar v Γ@.  Pre:
--
-- * @v@ is in scope in @Γ@
--
-- * If @Γ₁; v : A; Γ₂@, either @A = D t1 ⋯ tn@, where @D@ is a record
--   constructor, or @A@ is blocked.
--
-- Returns the context with @v@ η-expanded if @A@ isn't blocked, the
-- blocking metas if it is.
etaExpandContextVar
  :: (IsTerm t)
  => Ctx t -> Var
  -> TC t r s (Either MetaSet (Tel t, Subst t))
etaExpandContextVar ctx v = do
  let msg = do
        ctxDoc <- prettyM ctx
        return $
          "ctx:" //> ctxDoc $$
          "var:" //> PP.pretty v
  debugBracket "etaExpandContextVar" msg $ do
    let (ctx1, vType, tel2) = splitContext ctx v
    blocked <- isBlocked <$> whnf vType
    case blocked of
      Just mvs -> do
        return $ Left mvs
      Nothing -> do
        (tel2', acts) <- etaExpandVar vType tel2
        return $ Right (ctx1 `telAppend` tel2', acts)

-- | Expands a record-typed variable ranging over the given 'Tel',
-- returning a new telescope ranging over all the fields of the record
-- type and the old telescope with the variable substituted with a
-- constructed record, and a substitution for the old variable.
etaExpandVar
  :: (IsTerm t)
  => Type t
  -- ^ The type of the variable we're expanding.
  -> Tel t
  -> TC t r s (Tel t, Subst t)
etaExpandVar type_ tel = do
  App (Def tyCon) tyConPars0 <- whnfView type_
  Constant _ (Record dataCon projs) <- getDefinition tyCon
  DataCon _ _ dataConType <- getDefinition dataCon
  let Just tyConPars = mapM isApply tyConPars0
  appliedDataConType <- openContextual dataConType tyConPars
  (dataConPars0, _) <- assert_ ("etaExpandVar, unrollPiWithNames:" <+>) $
    unrollPiWithNames appliedDataConType (map (qNameName . pName . opndKey) projs)
  let dataConPars = telToCtx dataConPars0
  dataConT <- con dataCon =<< mapM var (ctxVars dataConPars)
  -- TODO isn't this broken?  don't we have to handle unit types
  -- specially like in metavar expansion?
  sub <- subInstantiate dataConT $ subWeaken (ctxLength dataConPars) subId
  tel' <- applySubst tel sub
  let telLen = telLength tel'
  return (dataConPars `telAppend` tel', subLift telLen sub)

-- | Divides a context at the given variable.
splitContext
  :: Ctx t -> Var -> (Ctx t, Type t, Tel t)
splitContext ctx00 v0 =
  go ctx00 (varIndex v0) T0
  where
    go ctx0 ix0 tel = case (ctx0, ix0) of
      (C0, _) ->
        __IMPOSSIBLE__
      (ctx :< (n', type_), ix) ->
        if ix > 0
        then go ctx (ix - 1) ((n', type_) :> tel)
        else (ctx, type_, tel)

type ProjectedVar t = (Var, [Opened Projection t])

-- | Codifies what is acceptable as an argument of a metavariable, if we
-- want to invert such metavariable.
data MetaArg t v
  = MVAVar v               -- This vars might be projected before
                           -- expanding the context.
  | MVARecord
      (Opened QName t)     -- Datacon name
      [MetaArg t v]        -- Arguments to the datacon
  deriving (Functor, Foldable, Traversable)

type MetaArg' t = MetaArg t (ProjectedVar t)

instance PrettyM t a => PrettyM t (MetaArg t a) where
  prettyM (MVAVar v) = do
    vDoc <- prettyM v
    return $ "MVAVar" <+> vDoc
  prettyM (MVARecord tyCon mvArgs) = do
    mvArgsDoc <- prettyM mvArgs
    tyConDoc <- prettyM tyCon
    return $ "MVARecord" <+> tyConDoc //> mvArgsDoc

-- | if @checkMetaElims els ==> args@, @length els == length args@.
checkMetaElims
  :: (IsTerm t) => [Elim (Term t)]
  -> TC t r s (Validation (Collect_ MetaSet) [MetaArg' t])
checkMetaElims elims = do
  case mapM isApply elims of
    Nothing   -> return $ Failure $ CFail ()
    Just args -> sequenceA <$> mapM checkMetaArg args

checkMetaArg
  :: (IsTerm t) => Term t -> TC t r s (Validation (Collect_ MetaSet) (MetaArg' t))
checkMetaArg arg = do
  blockedArg <- whnf arg
  let fallback = return $ Failure $ CFail ()
  case blockedArg of
    NotBlocked t -> do
      tView <- whnfView =<< etaContract t
      case tView of
        App (Var v) vArgs -> do
          case mapM isProj vArgs of
            Just ps -> return $ pure $ MVAVar (v, ps)
            Nothing -> fallback
        Con dataCon recArgs -> do
          DataCon tyCon _ _ <- getDefinition dataCon
          tyConDef <- getDefinition tyCon
          case tyConDef of
            Constant _ (Record _ _) -> do
              recArgs'  <- sequenceA <$> mapM checkMetaArg recArgs
              return $ MVARecord tyCon <$> recArgs'
            _ -> do
              fallback
        _ -> do
          fallback
    BlockingHead mv _ -> do
      return $ Failure $ CCollect $ HS.singleton mv
    BlockedOn mvs _ _ -> do
      return $ Failure $ CCollect mvs

-- | η-contracts a term (both records and lambdas).
etaContract :: forall t r s. (IsTerm t) => Term t -> TC t r s (Term t)
etaContract t0 = fmap (fromMaybe t0) $ runMaybeT $ do
  t0View <- lift $ whnfView t0
  case t0View of
    -- TODO it should be possible to do it also for constructors
    Lam body -> do
      App h elims@(_:_) <- lift $ whnfView =<< etaContract body
      Apply t <- return $ last elims
      App (Var v) [] <- lift $ whnfView t
      guard $ varIndex v == 0
      t' <- lift $ strengthen_ 1 =<< app h (init elims)
      return t'
    Con dataCon args -> do
      DataCon tyCon _ _ <- lift $ getDefinition dataCon
      Constant _ (Record _ fields) <- lift $ getDefinition tyCon
      guard $ length args == length fields
      (t : ts) <- sequence (zipWith isRightProjection fields args)
      guard =<< (and <$> lift (mapM (synEq t) ts))
      return t
    _ ->
      mzero
  where
    isRightProjection p t = do
      App h elims@(_ : _) <- lift $ whnfView =<< etaContract t
      Proj p' <- return $ last elims
      guard $ opndKey p == opndKey p'
      lift $ nf =<< app h (init elims)

-- Metavar inversion
------------------------------------------------------------------------

-- | Wraps the given term 'n' times.
lambdaAbstract :: (IsTerm t) => Natural -> Term t -> TC t r s (Term t)
lambdaAbstract 0 t = return t
lambdaAbstract n t = (lam <=< lambdaAbstract (n - 1)) t

data InvertMeta t = InvertMeta
  { imvSubst :: [(Var, Term t)]
    -- ^ A substitution from variables in equated term to variables by
    -- the metavariable to terms in the context abstracted by the
    -- metavariable.
  , imvAbstractions :: Natural
    -- ^ How many variables the metas abstracts.
  }

instance PrettyM  t (InvertMeta t) where
  prettyM (InvertMeta ts vs) = do
    ts' <- forM ts $ \(v, t) -> do
      tDoc <- prettyM t
      return $ PP.pretty (v, tDoc)
    return $ PP.list ts' $$ PP.pretty vs

invertMetaVars :: InvertMeta t -> [Var]
invertMetaVars (InvertMeta sub _) = map fst sub

invertMeta
  :: (IsTerm t)
  => Ctx t -> [Elim (Term t)]
  -> TC t r s (Either (Collect_ MetaSet) (Ctx t, Subst t, InvertMeta t))
invertMeta ctx elims = do
  let msg = do
        ctxDoc <- prettyM ctx
        elimsDoc <- prettyM elims
        return $
          "ctx:" //> ctxDoc $$
          "elims:" //> elimsDoc
  debugBracket "invertMeta" msg $ runExceptT $ do
    mvArgs <- ExceptT $ fmap validationToEither $ checkMetaElims elims
    (ctx', mvArgs', acts) <- lift $ removeProjections ctx mvArgs
    lift $ whenDebug $ unless (subNull acts) $ do
      debug "removeProjections" $ do
        ctx'Doc <- prettyM ctx'
        mvArgs'Doc <- prettyM mvArgs'
        return $
          "new ctx:" //> ctx'Doc $$
          "args:" //> mvArgs'Doc
    mbInv <- lift $ checkPatternCondition mvArgs'
    case mbInv of
      Nothing  -> do
        throwE $ CFail ()
      Just inv -> do
        lift $ debug "inverted" $ do
          ctx'Doc <- prettyM ctx'
          actsDoc <- prettyM acts
          invDoc <- prettyM inv
          return $
            "ctx:" //> ctx'Doc $$
            "acts:" //> actsDoc $$
            "inversion:" //> invDoc
        return (ctx', acts, inv)

mvaApplyActions
  :: (MonadTerm t m) => Subst t -> MetaArg' t -> m (MetaArg' t)
mvaApplyActions acts (MVAVar (v, ps)) = do
  vt <- var v
  vt' <- applySubst vt acts
  App (Var v') elims <- whnfView =<< eliminate vt' (map Proj ps)
  let Just ps' = mapM isProj elims
  return $ MVAVar (v', ps')
mvaApplyActions acts (MVARecord n args) = do
  MVARecord n <$> mapM (mvaApplyActions acts) args

varApplyActions
  :: (IsTerm t) => Subst t -> Var -> TC t r s (MetaArg t Var)
varApplyActions acts v = do
  tView <- whnfView =<< ((`applySubst` acts) =<< var v)
  case tView of
    App (Var v') [] -> do
      return $ MVAVar v'
    Con c args -> do
      Success mvArgs <- sequenceA <$> mapM checkMetaArg args
      let mvArgs' = map (fmap (\(x, []) -> x)) mvArgs
      return $ MVARecord c mvArgs'
    _ -> do
      fatalError "impossible.varApplyActions"

removeProjections
  :: forall t r s.
     (IsTerm t)
  => Ctx t -> [MetaArg' t]
  -> TC t r s (Ctx t, [MetaArg t Var], Subst t)
removeProjections ctx0 mvArgs0 = do
    let msg = do
          ctxDoc <- prettyM ctx0
          mvArgsDoc <- prettyM mvArgs0
          return $
            "ctx:" //> ctxDoc $$
            "args:" //> mvArgsDoc
    debugBracket "removeProjections" msg $ go ctx0 mvArgs0
  where
    go :: Ctx t -> [MetaArg' t]
       -> TC t r s (Ctx t, [MetaArg t Var], Subst t)
    go ctx [] = do
      return (ctx, [], subId)
    go ctx (MVAVar (v, []) : mvArgs) = do
      (ctx', mvArgs', tActs) <- go ctx mvArgs
      mvArg <- varApplyActions tActs v
      return (ctx', mvArg : mvArgs', tActs)
    go ctx1 (MVAVar (v, (p : ps)) : mvArgs) = do
      Right (ctx2, tActs) <- etaExpandContextVar ctx1 v
      t <- (`eliminate` [Proj p]) =<< var v
      App (Var v') [] <- whnfView =<< applySubst t tActs
      mvArgs' <- mapM (mvaApplyActions tActs) mvArgs
      (ctx3, mvArgs'', tActs') <- go (telToCtx ctx2) (MVAVar (v', ps) : mvArgs')
      tActs'' <- subCompose tActs' tActs
      return (ctx3, mvArgs'', tActs'')
    go ctx1 (MVARecord tyCon mvArgs1 : mvArgs2) = do
      (ctx2, mvArgs1', tActs1) <- go ctx1 mvArgs1
      (ctx3, mvArgs2', tActs2) <- go ctx2 mvArgs2
      tActs3 <- subCompose tActs2 tActs1
      return (ctx3, MVARecord tyCon mvArgs1' : mvArgs2', tActs3)

-- | Returns an inversion if the pattern condition is respected for the
-- given 'MetaArg's.
checkPatternCondition
  :: forall t r s. (IsTerm t)
  => [MetaArg t Var] -> TC t r s (Maybe (InvertMeta t))
checkPatternCondition mvArgs = do
  let allVs = concatMap toList mvArgs
  let linear = length allVs == fromIntegral (Set.size (Set.fromList allVs))
  if linear
    then do
      vs <- mapM var $ reverse [mkVar "_" ix | (ix, _) <- zip [0..] mvArgs]
      subs <- projectRecords $ zip mvArgs vs
      return $ Just $ InvertMeta subs (length vs)
    else do
      return $ Nothing
  where
    projectRecords xs = concat <$> mapM (uncurry projectRecord) xs

    projectRecord :: MetaArg t Var -> Term t -> TC t r s [(Var, Term t)]
    projectRecord (MVAVar v) t = do
      return [(v, t)]
    projectRecord (MVARecord tyCon mvArgs') t = do
      Constant _ (Record _ fields) <- getDefinition tyCon
      mvArgs'' <- forM (zip mvArgs' fields) $ \(mvArg, proj) ->
        (mvArg, ) <$> eliminate t [Proj proj]
      projectRecords mvArgs''

-- | Takes a meta inversion and applies it to a term.  Fails returning
--   a 'Var' if that 'Var' couldn't be substituted in the term -- in
--   other word if the term contains variables not present in the
--   substitution.
applyInvertMeta
  :: forall t r s.
     (IsTerm t)
  => Ctx t -> InvertMeta t -> Term t
  -> TC t r s (Validation (Collect Var MetaSet) (MetaBody t))
applyInvertMeta ctx (InvertMeta sub vsNum) t = do
  let fallback = fmap (MetaBody vsNum) <$> applyInvertMetaSubst sub t
  let dontTouch = return $ Success $ MetaBody vsNum t
  -- Optimization: if the substitution is the identity, and if the free
  -- variables in the term are a subset of the variables that the
  -- substitution covers, don't touch the term.
  isId <- isIdentity sub
  if isId
    then do
      let vs = Set.fromList (map fst sub)
      if Set.size vs == Prelude.length (ctxVars ctx)
        then dontTouch
        else do
          fvs <- freeVars t
          if fvAll fvs `Set.isSubsetOf` vs
            then dontTouch
            else fallback
    else fallback
  where
    isIdentity :: [(Var, Term t)] -> TC t r s Bool
    isIdentity [] = do
      return True
    isIdentity ((v, u) : sub') = do
      tView <- whnfView u
      case tView of
        App (Var v') [] | v == v' -> isIdentity sub'
        _                         -> return False

applyInvertMetaSubst
  :: forall t r s.
     (IsTerm t)
  => [(Var, Term t)]
  -- ^ Inversion from variables outside to terms inside
  -> Term t
  -- ^ Term outside
  -> TC t r s (Validation (Collect Var MetaSet) (Term t))
  -- ^ Either we fail with a variable that isn't present in the
  -- substitution, or we return a new term.
applyInvertMetaSubst sub t0 =
  flip go t0 $ \v -> return $ maybe (Left v) Right (lookup v sub)
  where
    lift' :: (Var -> TC t r s (Either Var (Term t)))
          -> (Var -> TC t r s (Either Var (Term t)))
    lift' f v0 = case strengthenVar_ 1 v0 of
      Nothing ->
        Right <$> var v0
      Just v -> do
        e <- f v
        case e of
          Left v' -> return $ Left v'
          Right t -> Right <$> weaken_ 1 t

    go :: (Var -> TC t r s (Either Var (Term t))) -> Term t
       -> TC t r s (Validation (Collect Var MetaSet) t)
    go invert t = do
      tView <- whnfView t
      case tView of
        Lam body -> do
          traverse lam =<< go (lift' invert) body
        Pi dom cod -> do
          dom' <- go invert dom
          cod' <- go (lift' invert) cod
          sequenceA $ pi <$> dom' <*> cod'
        Equal type_ x y -> do
          type' <- go invert type_
          x' <- go invert x
          y' <- go invert y
          sequenceA $ equal <$> type' <*> x' <*> y'
        Refl ->
          return $ pure refl
        Con dataCon args -> do
          args' <- mapM (go invert) args
          sequenceA $ con dataCon <$> sequenceA args'
        Set ->
          return $ pure set
        App h elims -> do
          let goElim (Apply t') = fmap Apply <$> go invert t'
              goElim (Proj p)   = return $ pure $ Proj p
          resElims <- sequenceA <$> mapM goElim elims
          let fallback = sequenceA $ app h <$> resElims
          let checkBlocking bl = case resElims of
                Failure (CCollect mvs) ->
                  return $ Failure $ CCollect $ HS.insert bl mvs
                Failure (CFail _) ->
                  return $ Failure $ CCollect $ HS.singleton bl
                _ ->
                  fallback
          case h of
            Meta mv -> do
              checkBlocking mv
            Var v -> do
              inv <- invert v
              sequenceA $ eliminate <$> either (Failure . CFail) pure inv <*> resElims
            Def _ -> do
              fallback
            J -> do
              fallback

-- Various
------------------------------------------------------------------------

-- | @killArgs α kills@ instantiates @α@ so that it discards the
--   arguments indicated by @kills@.
killArgs :: (IsTerm t) => Meta -> [Named Bool] -> TC t r s (MetaBody t)
killArgs newMv kills = do
  let vs = reverse [ mkVar n ix
                   | (ix, Named n kill) <- zip [0..] (reverse kills), not kill
                   ]
  body <- meta newMv . map Apply =<< mapM var vs
  return $ MetaBody (length kills) body

-- | If @t = α ts@ and @α : Δ -> D us@ where @D@ is some record type, it
-- will instantiate @α@ accordingly.
etaExpandMeta :: forall t r s. (IsTerm t) => Term t -> TC t r s (Term t)
etaExpandMeta t = do
  let fallback = do
        debug_ "didn't expand meta" ""
        return t
  debugBracket "etaExpandMeta" (prettyM t) $ do
    mbT <- runMaybeT $ do
      -- TODO duplication between this and 'instantiateDataCon'
      App (Meta mv) elims <- lift $ whnfView t
      mvType <- lift $ getMetaType mv
      (telMvArgs, endType) <- lift $ unrollPi mvType
      App (Def tyCon) tyConArgs0 <- lift $ whnfView endType
      Constant _ (Record dataCon _) <- lift $ getDefinition tyCon
      lift $ do
        DataCon _ _ dataConType <- getDefinition dataCon
        let Just tyConArgs = mapM isApply tyConArgs0
        appliedDataConType <- openContextual dataConType tyConArgs
        (dataConArgsTel, _) <- unrollPi appliedDataConType
        dataConArgs <- createMvsPars (telToCtx telMvArgs) dataConArgsTel
        mvT <- con dataCon dataConArgs
        let mvb = MetaBody (telLength telMvArgs) mvT
        instantiateMeta mv mvb
        mvT' <- metaBodyToTerm mvb
        eliminate mvT' elims
    case mbT of
      Just t' -> return t'
      Nothing -> fallback

-- | @etaExpand A t@ η-expands term @t@.
etaExpand :: forall t r s. (IsTerm t) => Type t -> Term t -> TC t r s (Term t)
etaExpand type_ t0 = do
  -- TODO should we do this here?
  t <- etaExpandMeta t0
  let fallback = do
        debug_ "didn't expand" ""
        return t
  let expanded t' = do
        debug "expanded" $ prettyM t'
        return t'
  let msg = do
        typeDoc <- prettyM type_
        tDoc <- prettyM t
        return $
          "type:" //> typeDoc $$
          "term:" //> tDoc
  debugBracket "etaExpand" msg $ do
    typeView <- whnfView type_
    case typeView of
      App (Def tyCon) _ -> do
        tyConDef <- getDefinition tyCon
        case tyConDef of
          Constant _ (Record dataCon projs) -> do
            tView <- whnfView t
            case tView of
              -- Optimization: if it's already of the right shape, do nothing
              Con _ _ -> do
                fallback
              _ -> do
                ts <- mapM (\p -> eliminate t [Proj p]) projs
                expanded =<< con dataCon ts
          _ -> do
            fallback
      Pi _ cod -> do
        name <- getAbsName_ cod
        v <- var $ boundVar name
        tView <- whnfView t
        -- Expand only if it's not a λ-function
        case tView of
          Lam _ -> do
            fallback
          _ -> do
            t' <- weaken_ 1 t
            t'' <- lam =<< eliminate t' [Apply v]
            expanded t''
      _ -> do
        fallback

-- | @intersectVars us vs@ checks whether all relevant elements in @us@
--   and @vs@ are variables, and if yes, returns a prune list which says
--   @True@ for arguments which are different and can be pruned.
intersectVars :: (IsTerm t) => [Elim t] -> [Elim t] -> TC t r s (Maybe [Named Bool])
intersectVars els1 els2 = runMaybeT $ mapM (uncurry areVars) $ zip els1 els2
  where
    areVars (Apply t1) (Apply t2) = do
      t1View <- lift $ whnfView t1
      t2View <- lift $ whnfView t2
      case (t1View, t2View) of
        (App (Var v1) [], App (Var v2) []) -> return $ (v1 /= v2) <$ unVar v1 -- prune different vars
        (_,               _)               -> mzero
    areVars _ _ =
      mzero

{-
-- | @instantiateDataCon α c@ makes it so that @α := c β₁ ⋯ βₙ@, where
--   @c@ is a data constructor.
--
--   Pre: @α : Δ → D t₁ ⋯ tₙ@, where @D@ is the fully applied type
--   constructor for @c@.
instantiateDataCon
  :: (IsTerm t)
  => Meta
  -> Opened Name t
  -- ^ Name of the datacon
  -> TC t r s (Closed (Term t))
instantiateDataCon mv dataCon = do
  mvType <- getMetaType mv
  (telMvArgs, endType') <- unrollPi mvType
  DataCon tyCon _ dataConType <- getDefinition dataCon
  -- We know that the metavariable must have the right type (we have
  -- typechecked the arguments already).
  App (Def tyCon') tyConArgs0 <- whnfView endType'
  Just tyConArgs <- return $ mapM isApply tyConArgs0
  True <- synEq tyCon tyCon'
  appliedDataConType <- openContextual dataConType tyConArgs
  (dataConArgsTel, _) <- unrollPi appliedDataConType
  dataConArgs <- createMvsPars (telToCtx telMvArgs) dataConArgsTel
  mvT <- con dataCon dataConArgs
  let mi = MetaBody (telLength telMvArgs) mvT
  -- given the usage, here we know that the body is going to be well typed.
  -- TODO make sure that the above holds.
  instantiateMeta mv mi
  metaBodyToTerm mi
-}

-- | @createMvsPars Γ Δ@ unrolls @Δ@ and creates a metavariable for
--   each of the elements.
createMvsPars
  :: (IsTerm t) => Ctx t -> Tel (Type t) -> TC t r s [Term t]
createMvsPars ctx0 tel0 = go ctx0 tel0
  where
    go _ T0 =
      return []
    go ctx ((_, type') :> tel) = do
      mv  <- addMetaInCtx ctx type'
      mvs <- go ctx =<< instantiate_ tel mv
      return (mv : mvs)

-- | Applies a projection to a term, and returns the new term and the
--   new type.
applyProjection
  :: (IsTerm t)
  => Opened Projection t
  -> Term t
  -- ^ Head
  -> Type t
  -- ^ Type of the head
  -> TC t r s (Term t, Type t)
applyProjection proj h type_ = do
  Projection _ tyCon projType <- getDefinition $ first pName proj
  h' <- eliminate h [Proj proj]
  App (Def tyCon') tyConArgs0 <- whnfView type_
  True <- synEq tyCon tyCon'
  let Just tyConArgs = mapM isApply tyConArgs0
  appliedProjType <- openContextual projType tyConArgs
  Pi _ endType <- whnfView appliedProjType
  endType' <- instantiate_ endType h
  return (h', endType')

headType
  :: (IsTerm t)
  => Ctx t -> Head t -> TC t r s (Type t)
headType ctx h = case h of
  Var v   -> ctxGetVar v ctx
  Def f   -> definitionType =<< getDefinition f
  Meta mv -> getMetaType mv
  J       -> return typeOfJ

isRecordConstr :: (IsTerm t) => Opened QName t -> TC t r s Bool
isRecordConstr dataCon = do
  def' <- getDefinition dataCon
  case def' of
    DataCon tyCon _ _ -> isRecordType tyCon
    _                 -> return False

isRecordType :: (IsTerm t) => Opened QName t -> TC t r s Bool
isRecordType tyCon = do
  def' <- getDefinition tyCon
  return $ case def' of
    Constant _ (Record _ _) -> True
    _                       -> False
