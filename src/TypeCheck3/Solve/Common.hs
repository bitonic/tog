{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
module TypeCheck3.Solve.Common where

import qualified Prelude
import           Control.Monad.Trans.Maybe        (MaybeT(MaybeT), runMaybeT)
import qualified Data.HashSet                     as HS
import qualified Data.Set                         as Set
import           Data.Tree                        (Tree(Node), subForest, rootLabel, Forest)

import           Instrumentation
import           Syntax
import           Prelude.Extended
import           PrettyPrint                      (($$), (<+>), (//>))
import qualified PrettyPrint                      as PP
import           Term
import qualified Term.Context                     as Ctx
import qualified Term.Telescope                   as Tel
import qualified Term.Subst                as Sub
import           TypeCheck3.Common
import           TypeCheck3.Monad
import           TypeCheck3.Check

-- Pruning
------------------------------------------------------------------------

{-# WARNING curryMetaVar "Remove this, do the unrolling on-demand in prune." #-}
-- | @curryMetaVar t@ checks if @t = α ts@ and for every argument
-- of the metavar which is a record type it splits it up in separate
-- arguments, one for each field.
curryMetaVar
  :: forall t s. (IsTerm t) => Term t -> TC t s (Term t)
curryMetaVar t = do
  let msg = do
        tDoc <- prettyM t
        return $
          "term:" //> tDoc
  debugBracket "curryMetaVar" msg $ fmap (fromMaybe t) $ runMaybeT $ do
    App (Meta mv) _ <- lift $ whnfView t
    (ctx, mvType) <- lift $ unrollPi =<< getMetaVarType mv
    (True, args0, newMvType) <- lift $ go (Tel.tel ctx) mvType
    lift $ do
      let abstractions = length args0
      args <- toArgs args0
      newMv <- addMetaVar newMvType
      mvT <- app (Meta newMv) (map Apply args)
      let mi = MetaVarBody abstractions mvT
      debug "unrolled" $ do
        mvTypeDoc <- prettyM =<< Ctx.pi ctx mvType
        newMvTypeDoc <- prettyM newMvType
        mvTDoc <- prettyM =<< metaVarBodyToTerm mi
        return $
          "old type:" //> mvTypeDoc $$
          "new type:" //> newMvTypeDoc $$
          "term:" //> mvTDoc
      instantiateMetaVar mv mi
      -- Now we return the old type, which normalized will give the new
      -- mv.
      return t
  where
    treePaths :: Tree a -> [[a]]
    treePaths tr | null (subForest tr) = [[rootLabel tr]]
    treePaths tr = concatMap (map (rootLabel tr :) . treePaths)  (subForest tr)

    toArgs :: MetaVarArgs -> TC t s [Term t]
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

    go :: Tel.Tel t -> Type t -> TC t s (Bool, MetaVarArgs, Type t)
    go Tel.Empty type_ = do
      return (False, [], type_)
    go (Tel.Cons (n, dom) tel) type0 = do
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
            Constant (Record dataCon projs) _ -> do
              let Just tyConPars = mapM isApply elims
              DataCon _ _ dataConTypeTel dataConType <- getDefinition dataCon
              appliedDataConType <- Tel.discharge dataConTypeTel dataConType tyConPars
              debug_ "tyConPars" $ PP.text $ show $ show tyConPars
              (dataConPars, _) <-
                assert_ ("curryMetaVar, unrollPiWithNames:" <+>) $
                unrollPiWithNames appliedDataConType (map pName projs)
              let numDataConPars = Ctx.length dataConPars
              recordTerm <- con dataCon =<< mapM var (Ctx.vars dataConPars)
              let telLen = Tel.length tel
              let weakenBy = numDataConPars
              if weakenBy <= 0
                -- This means that the type was unit.
                then do
                  tel' <- instantiate_ tel recordTerm
                  type1 <- applySubst type0 . Sub.lift telLen =<< Sub.singleton recordTerm
                  (_, args, type2) <- go (dataConPars Tel.++ tel') type1
                  return (True, Nothing : args, type2)
                else do
                  sub <- Sub.instantiate recordTerm $ Sub.weaken numDataConPars Sub.id
                  tel' <- applySubst tel sub
                  type1 <- applySubst type0 $ Sub.lift telLen sub
                  (_, args, type2) <- go (dataConPars Tel.++ tel') type1
                  let (argsL, argsR) = splitAt (length projs) args
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
    -> TC t s (Term t)
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
    -> TC t s (Term t)
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
      mvT <- metaVar mv elims
      -- TODO do expansion/currying more lazily, and optimize by first
      -- checking if we need to do anything at all.
      mvTView <- whnfView =<< etaExpandMeta =<< curryMetaVar mvT
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

type MetaVarArgs = [Maybe (Var, Forest Projection)]

-- | @prune vs α es@ tries to prune all the variables in @es@ that are
--   not in @vs@, by instantiating @α@.  If we managed to prune
--   anything returns 'Just', 'Nothing' if we can't prune or no prune
--   is needed.
prune
    :: forall t s.
       (IsTerm t)
    => Set.Set Var           -- ^ allowed vars
    -> MetaVar
    -> [Elim (Term t)]       -- ^ Arguments to the metavariable
    -> TC t s (Maybe (Closed (Term t)))
prune allowedVs oldMv elims = do
  -- TODO can we do something more if we have projections?
  runMaybeT $ do
    args <- MaybeT $ return $ mapM isApply elims
    kills0 <- MaybeT $ sequence <$> mapM (shouldKill allowedVs) args
    guard (or kills0)
    let msg = do
          mvTypeDoc <- prettyM =<< getMetaVarType oldMv
          elimsDoc <- prettyM elims
          return $
            "metavar type:" //> mvTypeDoc $$
            "metavar:" <+> PP.pretty oldMv $$
            "elims:" //> elimsDoc $$
            "to kill:" //> PP.pretty kills0 $$
            "allowed vars:" //> PP.pretty (Set.toList allowedVs)
    MaybeT $ debugBracket "prune" msg $ runMaybeT $ do
      oldMvType <- lift $ getMetaVarType oldMv
      (newMvType, kills1) <- lift $ createNewMeta oldMvType kills0
      lift $ debug_ "new kills" $ PP.pretty (map unNamed kills1)
      guard (any unNamed kills1)
      newMv <- lift $ addMetaVar newMvType
      mi <- lift $ killArgs newMv kills1
      lift $ instantiateMetaVar oldMv mi
      lift $ metaVarBodyToTerm mi
  where
    -- We build a pi-type with the non-killed types in.  This way, we
    -- can analyze the dependency between arguments and avoid killing
    -- things that later arguments depend on.
    --
    -- At the end of the type we put both the new metavariable and the
    -- remaining type, so that this dependency check will be performed
    -- on it as well.
    createNewMeta
      :: Type t -> [Bool] -> TC t s (Type t, [Named Bool])
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
  => Set.Set Var -> Term t -> TC t s (Maybe Bool)
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
        Constant{}    -> return False
        DataCon{}     -> fatalError $ "impossible.isNeutral: constructor " ++ show f
        Projection{}  -> fatalError $ "impossible.isNeutral: projection " ++ show f
        Function{}    -> return True
        -- TODO: more precise analysis
        -- We need to check whether a function is stuck on a variable
        -- (not meta variable), but the API does not help us...

-- Tools useful for expanding of contexts.
------------------------------------------------------------------------

-- | Checks whether an eliminator is a a projected variables (because
--   we can expand those).
isProjectedVar :: (IsTerm t) => Elim t -> MaybeT (TC t s) (Var, Name)
isProjectedVar elim = do
  Apply t <- return elim
  App (Var v) vElims <- lift $ whnfView t
  projName : _ <- forM vElims $ \vElim -> do
    Proj p <- return vElim
    return $ pName p
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
  -> TC t s (Either MetaVarSet (Ctx t, Subst t))
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
        return $ Right (ctx1 Ctx.++ Tel.unTel tel2', acts)

-- | Expands a record-typed variable ranging over the given 'Tel.Tel',
-- returning a new telescope ranging over all the fields of the record
-- type and the old telescope with the variable substituted with a
-- constructed record, and a substitution for the old variable.
etaExpandVar
  :: (IsTerm t)
  => Type t
  -- ^ The type of the variable we're expanding.
  -> Tel t
  -> TC t s (Tel.Tel t, Subst t)
etaExpandVar type_ tel = do
  App (Def tyCon) tyConPars0 <- whnfView type_
  Constant (Record dataCon projs) _ <- getDefinition tyCon
  DataCon _ _ dataConTypeTel dataConType <- getDefinition dataCon
  let Just tyConPars = mapM isApply tyConPars0
  appliedDataConType <- Tel.discharge dataConTypeTel dataConType tyConPars
  (dataConPars, _) <- assert_ ("etaExpandVar, unrollPiWithNames:" <+>) $
    unrollPiWithNames appliedDataConType (map pName projs)
  dataConT <- con dataCon =<< mapM var (Ctx.vars dataConPars)
  -- TODO isn't this broken?  don't we have to handle unit types
  -- specially like in metavar expansion?
  sub <- Sub.instantiate dataConT $ Sub.weaken (Ctx.length dataConPars) Sub.id
  tel' <- applySubst tel sub
  let telLen = Tel.length tel'
  return (dataConPars Tel.++ tel', Sub.lift telLen sub)

-- | Divides a context at the given variable.
splitContext
  :: Ctx t -> Var -> (Ctx t, Type t, Tel t)
splitContext ctx00 v0 = go ctx00 (varIndex v0) Tel.Empty
  where
    go ctx0 ix0 tel = case (ctx0, ix0) of
      (Ctx.Empty, _) ->
        error "impossible.splitContext: var out of scope"
      (Ctx.Snoc ctx (n', type_), ix) ->
        if ix > 0
        then go ctx (ix - 1) (Tel.Cons (n', type_) tel)
        else (ctx, type_, tel)

type ProjectedVar = (Var, [Projection])

-- | Codifies what is acceptable as an argument of a metavariable, if we
-- want to invert such metavariable.
data MetaVarArg v
  = MVAVar v               -- This vars might be projected before
                           -- expanding the context.
  | MVARecord
      Name                 -- Datacon name
      [MetaVarArg v]       -- Arguments to the datacon
  deriving (Functor, Foldable, Traversable)

type MetaVarArg' = MetaVarArg ProjectedVar

instance (PP.Pretty v) => PP.Pretty (MetaVarArg v) where
  pretty (MVAVar v) =
    "MVAVar" <+> PP.pretty v
  pretty (MVARecord tyCon mvArgs) =
    "MVARecord" <+> PP.pretty tyCon //> PP.pretty mvArgs

-- | if @checkMetaVarElims els ==> args@, @length els == length args@.
checkMetaVarElims
  :: (IsTerm t) => [Elim (Term t)] -> TC t s (TermTraverse' [MetaVarArg'])
checkMetaVarElims elims = do
  case mapM isApply elims of
    Nothing   -> return $ TTFail ()
    Just args -> sequenceA <$> mapM checkMetaVarArg args

checkMetaVarArg
  :: (IsTerm t) => Term t -> TC t s (TermTraverse' MetaVarArg')
checkMetaVarArg arg = do
  blockedArg <- whnf arg
  let fallback = return $ TTFail ()
  case blockedArg of
    NotBlocked t -> do
      tView <- whnfView =<< etaContract t
      case tView of
        App (Var v) vArgs -> do
          case mapM isProj vArgs of
            Just ps -> return $ pure $ MVAVar (v, ps)
            Nothing -> fallback
        Con dataCon recArgs -> do
          DataCon tyCon _ _ _ <- getDefinition dataCon
          tyConDef <- getDefinition tyCon
          case tyConDef of
            Constant (Record _ _) _ -> do
              recArgs'  <- sequenceA <$> mapM checkMetaVarArg recArgs
              return $ MVARecord tyCon <$> recArgs'
            _ -> do
              fallback
        _ -> do
          fallback
    MetaVarHead mv _ -> do
      return $ TTMetaVars $ HS.singleton mv
    BlockedOn mvs _ _ -> do
      return $ TTMetaVars mvs

-- | η-contracts a term (both records and lambdas).
etaContract :: (IsTerm t) => Term t -> TC t s (Term t)
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
      DataCon tyCon _ _ _ <- lift $ getDefinition dataCon
      Constant (Record _ fields) _ <- lift $ getDefinition tyCon
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
      guard $ p == p'
      lift $ nf =<< app h (init elims)

-- Metavar inversion
------------------------------------------------------------------------

-- | Wraps the given term 'n' times.
lambdaAbstract :: (IsTerm t) => Natural -> Term t -> TC t s (Term t)
lambdaAbstract 0 t = return t
lambdaAbstract n t = (lam <=< lambdaAbstract (n - 1)) t

data InvertMetaVar t = InvertMetaVar
  { imvSubst :: [(Var, Term t)]
    -- ^ A substitution from variables in equated term to variables by
    -- the metavariable to terms in the context abstracted by the
    -- metavariable.
  , imvAbstractions :: Natural
    -- ^ How many variables the metas abstracts.
  }

instance PrettyM  t (InvertMetaVar t) where
  prettyM (InvertMetaVar ts vs) = do
    ts' <- forM ts $ \(v, t) -> do
      tDoc <- prettyM t
      return $ PP.pretty (v, tDoc)
    return $ PP.list ts' $$ PP.pretty vs

invertMetaVarVars :: InvertMetaVar t -> [Var]
invertMetaVarVars (InvertMetaVar sub _) = map fst sub

invertMetaVar
  :: (IsTerm t)
  => Ctx t -> [Elim (Term t)]
  -> TC t s (TermTraverse' (Ctx t, Subst t, InvertMetaVar t))
invertMetaVar ctx elims = do
  let msg = do
        ctxDoc <- prettyM ctx
        elimsDoc <- prettyM elims
        return $
          "ctx:" //> ctxDoc $$
          "elims:" //> elimsDoc
  debugBracket "invertMetaVar" msg $ runTermTraverseT $ do
    mvArgs <- TTT $ checkMetaVarElims elims
    (ctx', mvArgs', acts) <- lift $ removeProjections ctx mvArgs
    lift $ whenDebug $ unless (Sub.null acts) $ do
      debug "removeProjections" $ do
        ctx'Doc <- prettyM ctx'
        return $
          "new ctx:" //> ctx'Doc $$
          "args:" //> PP.pretty mvArgs'
    mbInv <- lift $ checkPatternCondition mvArgs'
    case mbInv of
      Nothing  -> do
        hoistTT $ TTFail ()
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
  :: (IsTerm t, MonadTerm t m) => Subst t -> MetaVarArg' -> m MetaVarArg'
mvaApplyActions acts (MVAVar (v, ps)) = do
  vt <- var v
  vt' <- applySubst vt acts
  App (Var v') elims <- whnfView =<< eliminate vt' (map Proj ps)
  let Just ps' = mapM isProj elims
  return $ MVAVar (v', ps')
mvaApplyActions acts (MVARecord n args) = do
  MVARecord n <$> mapM (mvaApplyActions acts) args

varApplyActions
  :: (IsTerm t) => Subst t -> Var -> TC t s (MetaVarArg Var)
varApplyActions acts v = do
  tView <- whnfView =<< ((`applySubst` acts) =<< var v)
  case tView of
    App (Var v') [] -> do
      return $ MVAVar v'
    Con c args -> do
      TTOK mvArgs <- sequenceA <$> mapM checkMetaVarArg args
      let mvArgs' = map (fmap (\(x, []) -> x)) mvArgs
      return $ MVARecord c mvArgs'
    _ -> do
      fatalError "impossible.varApplyActions"

removeProjections
  :: forall t s .
     (IsTerm t)
  => Ctx t -> [MetaVarArg']
  -> TC t s (Ctx t, [MetaVarArg Var], Subst t)
removeProjections ctx0 mvArgs0 = do
    let msg = do
          ctxDoc <- prettyM ctx0
          return $
            "ctx:" //> ctxDoc $$
            "args:" //> PP.pretty mvArgs0
    debugBracket "removeProjections" msg $ go ctx0 mvArgs0
  where
    go :: Ctx t -> [MetaVarArg']
       -> TC t s (Ctx t, [MetaVarArg Var], Subst t)
    go ctx [] = do
      return (ctx, [], Sub.id)
    go ctx (MVAVar (v, []) : mvArgs) = do
      (ctx', mvArgs', tActs) <- go ctx mvArgs
      mvArg <- varApplyActions tActs v
      return (ctx', mvArg : mvArgs', tActs)
    go ctx1 (MVAVar (v, (p : ps)) : mvArgs) = do
      Right (ctx2, tActs) <- etaExpandContextVar ctx1 v
      t <- (`eliminate` [Proj p]) =<< var v
      App (Var v') [] <- whnfView =<< applySubst t tActs
      mvArgs' <- mapM (mvaApplyActions tActs) mvArgs
      (ctx3, mvArgs'', tActs') <- go ctx2 (MVAVar (v', ps) : mvArgs')
      tActs'' <- Sub.compose tActs' tActs
      return (ctx3, mvArgs'', tActs'')
    go ctx1 (MVARecord tyCon mvArgs1 : mvArgs2) = do
      (ctx2, mvArgs1', tActs1) <- go ctx1 mvArgs1
      (ctx3, mvArgs2', tActs2) <- go ctx2 mvArgs2
      tActs3 <- Sub.compose tActs2 tActs1
      return (ctx3, MVARecord tyCon mvArgs1' : mvArgs2', tActs3)

-- | Returns an inversion if the pattern condition is respected for the
-- given 'MetaVarArg's.
checkPatternCondition
  :: forall t s. (IsTerm t)
  => [MetaVarArg Var] -> TC t s (Maybe (InvertMetaVar t))
checkPatternCondition mvArgs = do
  let allVs = concatMap toList mvArgs
  let linear = length allVs == fromIntegral (Set.size (Set.fromList allVs))
  if linear
    then do
      vs <- mapM var $ reverse [mkVar "_" ix | (ix, _) <- zip [0..] mvArgs]
      subs <- projectRecords $ zip mvArgs vs
      return $ Just $ InvertMetaVar subs (length vs)
    else do
      return $ Nothing
  where
    projectRecords xs = concat <$> mapM (uncurry projectRecord) xs

    projectRecord :: MetaVarArg Var -> Term t -> TC t s [(Var, Term t)]
    projectRecord (MVAVar v) t = do
      return [(v, t)]
    projectRecord (MVARecord tyCon mvArgs') t = do
      Constant (Record _ fields) _ <- getDefinition tyCon
      mvArgs'' <- forM (zip mvArgs' fields) $ \(mvArg, proj) ->
        (mvArg, ) <$> eliminate t [Proj proj]
      projectRecords mvArgs''

-- | Takes a meta inversion and applies it to a term.  Fails returning
--   a 'Var' if that 'Var' couldn't be substituted in the term -- in
--   other word if the term contains variables not present in the
--   substitution.
applyInvertMetaVar
  :: forall t s.
     (IsTerm t)
  => Ctx t -> InvertMetaVar t -> Term t
  -> TC t s (TermTraverse Var (MetaVarBody t))
applyInvertMetaVar ctx (InvertMetaVar sub vsNum) t = do
  let fallback = do
        tt <- applyInvertMetaSubst sub t
        case tt of
          TTFail v ->
            return $ TTFail v
          TTMetaVars mvs ->
            return $ TTMetaVars mvs
          TTOK t' -> do
            return $ TTOK $ MetaVarBody vsNum t'
  let dontTouch = do
        return $ TTOK $ MetaVarBody vsNum t
  -- Optimization: if the substitution is the identity, and if the free
  -- variables in the term are a subset of the variables that the
  -- substitution covers, don't touch the term.
  isId <- isIdentity sub
  if isId
    then do
      let vs = Set.fromList (map fst sub)
      if Set.size vs == Prelude.length (Ctx.vars ctx)
        then dontTouch
        else do
          fvs <- freeVars t
          if fvAll fvs `Set.isSubsetOf` vs
            then dontTouch
            else fallback
    else fallback
  where
    isIdentity :: [(Var, Term t)] -> TC t s Bool
    isIdentity [] = do
      return True
    isIdentity ((v, u) : sub') = do
      tView <- whnfView u
      case tView of
        App (Var v') [] | v == v' -> isIdentity sub'
        _                         -> return False

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
        Right <$> var v0
      Just v -> do
        e <- f v
        case e of
          Left v' -> return $ Left v'
          Right t -> Right <$> weaken_ 1 t

    go :: (Var -> TC t s (Either Var (Term t))) -> Term t
       -> TC t s (TermTraverse Var t)
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
          case (h, resElims) of
            (Meta mv, TTMetaVars mvs) ->
              return $ TTMetaVars $ HS.insert mv mvs
            (Meta mv, TTFail _) ->
              return $ TTMetaVars $ HS.singleton mv
            (Var v, _) -> do
              inv <- invert v
              sequenceA $ eliminate <$> either TTFail pure inv <*> resElims
            (Def f, _) ->
              sequenceA $ app (Def f) <$> resElims
            (J, _) ->
              sequenceA $ app J <$> resElims
            (Meta mv, _) ->
              sequenceA $ app (Meta mv) <$> resElims

-- Various
------------------------------------------------------------------------

-- | @killArgs α kills@ instantiates @α@ so that it discards the
--   arguments indicated by @kills@.
killArgs :: (IsTerm t) => MetaVar -> [Named Bool] -> TC t s (MetaVarBody t)
killArgs newMv kills = do
  let vs = reverse [ mkVar n ix
                   | (ix, Named n kill) <- zip [0..] (reverse kills), not kill
                   ]
  body <- metaVar newMv . map Apply =<< mapM var vs
  return $ MetaVarBody (length kills) body

-- | If @t = α ts@ and @α : Δ -> D us@ where @D@ is some record type, it
-- will instantiate @α@ accordingly.
etaExpandMeta :: forall t s. (IsTerm t) => Term t -> TC t s (Term t)
etaExpandMeta t = do
  let fallback = do
        debug_ "didn't expand meta" ""
        return t
  debugBracket "etaExpandMeta" (prettyM t) $ do
    mbT <- runMaybeT $ do
      -- TODO duplication between this and 'instantiateDataCon'
      App (Meta mv) elims <- lift $ whnfView t
      mvType <- lift $ getMetaVarType mv
      (_, endType) <- lift $ unrollPi mvType
      App (Def tyCon) _ <- lift $ whnfView endType
      Constant (Record dataCon _) _ <- lift $ getDefinition tyCon
      mvT :: Term t <- lift $ instantiateDataCon mv dataCon
      lift $ eliminate mvT elims
    case mbT of
      Just t' -> return t'
      Nothing -> fallback

-- | @etaExpand A t@ η-expands term @t@.
etaExpand :: forall t s. (IsTerm t) => Type t -> Term t -> TC t s (Term t)
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
          Constant (Record dataCon projs) _ -> do
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
intersectVars :: (IsTerm t) => [Elim t] -> [Elim t] -> TC t s (Maybe [Named Bool])
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

-- | @instantiateDataCon α c@ makes it so that @α := c β₁ ⋯ βₙ@, where
--   @c@ is a data constructor.
--
--   Pre: @α : Δ → D t₁ ⋯ tₙ@, where @D@ is the fully applied type
--   constructor for @c@.
instantiateDataCon
  :: (IsTerm t)
  => MetaVar
  -> Name
  -- ^ Name of the datacon
  -> TC t s (Closed (Term t))
instantiateDataCon mv dataCon = do
  mvType <- getMetaVarType mv
  (ctxMvArgs, endType') <- unrollPi mvType
  DataCon tyCon _ dataConTypeTel dataConType <- getDefinition dataCon
  -- We know that the metavariable must have the right type (we have
  -- typechecked the arguments already).
  App (Def tyCon') tyConArgs0 <- whnfView endType'
  Just tyConArgs <- return $ mapM isApply tyConArgs0
  True <- return $ tyCon == tyCon'
  appliedDataConType <- Tel.discharge dataConTypeTel dataConType tyConArgs
  (dataConArgsCtx, _) <- unrollPi appliedDataConType
  dataConArgs <- createMvsPars ctxMvArgs $ Tel.tel dataConArgsCtx
  mvT <- con dataCon dataConArgs
  let mi = MetaVarBody (length (Ctx.vars ctxMvArgs)) mvT
  -- given the usage, here we know that the body is going to be well typed.
  -- TODO make sure that the above holds.
  instantiateMetaVar mv mi
  metaVarBodyToTerm mi

-- | @createMvsPars Γ Δ@ unrolls @Δ@ and creates a metavariable for
--   each of the elements.
createMvsPars
  :: (IsTerm t) => Ctx t -> Tel.Tel (Type t) -> TC t s [Term t]
createMvsPars _ Tel.Empty =
  return []
createMvsPars ctx (Tel.Cons (_, type') tel) = do
  mv  <- addMetaVarInCtx ctx type'
  mvs <- createMvsPars ctx =<< instantiate_ tel mv
  return (mv : mvs)

-- | Applies a projection to a term, and returns the new term and the
--   new type.
applyProjection
  :: (IsTerm t)
  => Projection
  -> Term t
  -- ^ Head
  -> Type t
  -- ^ Type of the head
  -> TC t s (Term t, Type t)
applyProjection proj h type_ = do
  Projection _ tyCon projTypeTel projType <- getDefinition $ pName proj
  h' <- eliminate h [Proj proj]
  App (Def tyCon') tyConArgs0 <- whnfView type_
  let _assert@True = tyCon == tyCon'
  let Just tyConArgs = mapM isApply tyConArgs0
  appliedProjType <- Tel.discharge projTypeTel projType tyConArgs
  Pi _ endType <- whnfView appliedProjType
  endType' <- instantiate_ endType h
  return (h', endType')

headType
  :: (IsTerm t)
  => Ctx t -> Head -> TC t s (Type t)
headType ctx h = case h of
  Var v   -> Ctx.getVar v ctx
  Def f   -> definitionType =<< getDefinition f
  J       -> return typeOfJ
  Meta mv -> getMetaVarType mv

isRecordConstr :: (IsTerm t) => Name -> TC t s Bool
isRecordConstr dataCon = do
  def' <- getDefinition dataCon
  case def' of
    DataCon tyCon _ _ _ -> isRecordType tyCon
    _                   -> return False

isRecordType :: (IsTerm t) => Name -> TC t s Bool
isRecordType tyCon = do
  def' <- getDefinition tyCon
  return $ case def' of
    Constant (Record _ _) _ -> True
    _                       -> False
