{-# LANGUAGE OverloadedStrings #-}
module TypeCheck3.Solve.Common where

import           Prelude                          hiding (any, pi, mapM)

import           Control.Monad.Trans.Except       (ExceptT(ExceptT), runExceptT)
import           Control.Monad.Trans.Maybe        (MaybeT(MaybeT), runMaybeT)
import           Data.Traversable                 (mapM)
import qualified Data.HashSet                     as HS
import qualified Data.Set                         as Set
import           Data.Tree                        (Tree(Node), subForest, rootLabel, Forest)

import           Syntax
import           Prelude.Extended
import           PrettyPrint                      (($$), (<+>), (//>))
import qualified PrettyPrint                      as PP
import           Term
import qualified Term.Context                     as Ctx
import qualified Term.Signature                   as Sig
import qualified Term.Telescope                   as Tel
import           TypeCheck3.Common
import           TypeCheck3.Monad
import           TypeCheck3.Check

-- Pruning
------------------------------------------------------------------------

{-# WARNING unrollMetaVarArgs "Remove this, do the unrolling on-demand in prune." #-}
-- | @unrollMetaVarArgs t@ checks if @t = α ts@ and for every argument
-- of the metavar which is a record type it splits it up in separate
-- arguments, one for each field.
unrollMetaVarArgs
  :: forall t s. (IsTerm t) => Term t -> TC t s (Maybe (Term t))
unrollMetaVarArgs t = do
  let msg = do
        tDoc <- prettyTermM t
        return $
          "term:" //> tDoc
  debugBracket "unrollMetaVarArgs" msg $ runMaybeT $ do
    App (Meta mv) _ <- lift $ whnfView t
    (ctx, mvType) <- lift $ unrollPi =<< getMetaVarType mv
    (True, args0, newMvType) <- lift $ go (Tel.tel ctx) mvType
    lift $ do
      let abstractions = length args0
      args <- toArgs args0
      newMv <- addMetaVar newMvType
      mvT <- lambdaAbstract abstractions =<< app (Meta newMv) (map Apply args)
      debug "unrolled" $ do
        mvTypeDoc <- prettyTermM =<< Ctx.pi ctx mvType
        newMvTypeDoc <- prettyTermM newMvType
        mvTDoc <- prettyTermM mvT
        return $
          "old type:" //> mvTypeDoc $$
          "new type:" //> newMvTypeDoc $$
          "term:" //> mvTDoc
      instantiateMetaVar mv mvT
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
              appliedDataConType <- Tel.substs dataConTypeTel dataConType tyConPars
              (dataConPars, _) <-
                assert_ ("unrollMetaVarArgs, unrollPiWithNames:" <+>) $
                unrollPiWithNames appliedDataConType (map pName projs)
              let numDataConPars = Ctx.length dataConPars
              recordTerm <- con dataCon =<< mapM var (Ctx.vars dataConPars)
              let telLen = Tel.length tel
              let weakenBy = numDataConPars-1
              if weakenBy < 0
                -- This means that the type was unit.
                then do
                  Just tel' <- Tel.strengthen_ 1 =<< Tel.subst 0 recordTerm tel
                  recordTerm' <- weaken_ telLen recordTerm
                  Just type1 <- strengthen telLen 1 =<< subst telLen recordTerm' type0
                  (_, args, type2) <- go (dataConPars Tel.++ tel') type1
                  return (True, Nothing : args, type2)
                else do
                  tel' <- Tel.subst 0 recordTerm =<< Tel.weaken 1 weakenBy tel
                  recordTerm' <- weaken_ telLen recordTerm
                  type1 <- subst telLen recordTerm' =<< weaken (telLen+1) weakenBy type0
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
        tDoc <- prettyTermM t
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
      mbMvT <- unrollMetaVarArgs t
      case mbMvT of
        Nothing -> do
          mbMvT' <- prune vs mv elims
          case mbMvT' of
            Nothing  -> metaVar mv elims
            Just mvT -> eliminate mvT elims
        Just mvT -> do
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
prune allowedVs oldMv elims | Just args <- mapM isApply elims = do
  mbKills <- sequence <$> mapM (shouldKill allowedVs) args
  case mbKills of
    Just kills0 | or kills0 -> do
      let msg = do
            mvTypeDoc <- prettyTermM =<< getMetaVarType oldMv
            elimsDoc <- prettyListM elims
            return $
              "metavar type:" //> mvTypeDoc $$
              "metavar:" <+> PP.pretty oldMv $$
              "elims:" //> elimsDoc $$
              "to kill:" //> PP.pretty kills0 $$
              "allowed vars:" //> PP.pretty (Set.toList allowedVs)
      debugBracket "prune" msg $ do
        oldMvType <- getMetaVarType oldMv
        (newMvType, kills1) <- createNewMeta oldMvType kills0
        debug_ "new kills" $ PP.pretty (map unNamed kills1)
        if any unNamed kills1
          then do
            newMv <- addMetaVar newMvType
            mvT <- killArgs newMv kills1
            instantiateMetaVar oldMv mvT
            return $ Just mvT
          else do
            return Nothing
    _ -> do
      return Nothing
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
            domDoc <- prettyTermM domain
            typeDoc <- prettyTermM type'
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
              mbType <- strengthen_ 1 =<< nf type'
              case mbType of
                (Just type'') -> return (type'', named name True : kills')
                _             -> do debug_ "couldn't strengthen" ""
                                    notKilled
        _ ->
          fatalError "impossible.createNewMeta: metavar type too short"
prune _ _ _ = do
  -- TODO we could probably do something more.
  return Nothing

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
      neutr <- not <$> lift (isNeutral f =<< askSignature)
      if neutr then mzero else fallback
    _ ->
      fallback
  where
    fallback = lift $ do
      fvs <- freeVars t
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

-- Inverting metavars
------------------------------------------------------------------------

-- | An inversion is a substitution from to be used in the term we're
--   trying to instantiate a metavariable with. So if we have @α v₁ ⋯
--   vₙ = t@ we want to produce an inversion that makes sure that @t@
--   only contains variables in @v₁ ⋯ vₙ@, and that substitutes them
--   for what @α@ will abstract over.
--
--   Note that we need @[(Var, t)]@ instead of simply @[(Var, Var)]@
--   because we might substitute variables with data constructors of
--   records (so in @α v₁ ⋯ vₙ@ the vs can be also data constructors
--   of records).
data InvertMeta t =
  InvertMeta [(Var, t)]
             -- This 'Var' refers to a variable in the term equated to
             -- the metavariable
             Int
             -- How many variables the metavar abstracts.

invertMetaVars :: InvertMeta t -> [Var]
invertMetaVars (InvertMeta sub _) = map fst sub

instance PrettyM InvertMeta where
  prettyM (InvertMeta ts vs) = do
    ts' <- forM ts $ \(v, t) -> do
      tDoc <- prettyTermM t
      return $ PP.pretty (v, tDoc)
    return $ PP.list ts' $$ PP.pretty vs

-- | Tries to invert a metavariable given its parameters
--   (eliminators), providing a substitution for the term on the right
--   if it suceeds.  Doing so amounts to check if the pattern
--   condition is respected for the arguments, although we employ
--   various trick to get around it when the terms are not variables.
--   See doc for 'InvertMeta'.
--
--   'TTMetaVars' if the pattern condition check is blocked on a some
--   'MetaVar's.
--
--   'TTFail' if the pattern condition fails.
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
      res <- checkArgs . zip args =<< mapM var vs
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
      blockedArg <- whnf arg
      case blockedArg of
        -- If the argument is a variable, we are simply going to replace
        -- it with the corresponding variable in the body of the meta.
        NotBlocked t -> do
          tView <- whnfView t
          case tView of
            App (Var v0) [] ->
              return $ pure [(v0, v)]
            -- If the argument is a record, we're going to substitute
            -- the variable on the right with projected terms inside the
            -- body of the metavariable.
            Con dataCon recArgs -> do
              DataCon tyCon _ _ _ <- getDefinition dataCon
              tyConDef <- getDefinition tyCon
              case tyConDef of
                Constant (Record _ fields) _ -> do
                  recArgs' <- forM (zip recArgs fields) $ \(recArg, p) ->
                    (recArg, ) <$> eliminate v [Proj p]
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

-- | Takes a meta inversion and applies it to a term.  Fails returning
--   a 'Var' if that 'Var' couldn't be substituted in the term -- in
--   other word if the term contains variables not present in the
--   substitution.
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
lambdaAbstract n t = (lam <=< lambdaAbstract (n - 1)) t

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
  -> TC t s (Either MetaVarSet (Ctx t, [TermAction t]))
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
  -> TC t s (Tel.Tel t, [TermAction t])
etaExpandVar type_ tel = do
  App (Def tyCon) tyConPars0 <- whnfView type_
  Constant (Record dataCon projs) _ <- getDefinition tyCon
  DataCon _ _ dataConTypeTel dataConType <- getDefinition dataCon
  let Just tyConPars = mapM isApply tyConPars0
  appliedDataConType <- Tel.substs dataConTypeTel dataConType tyConPars
  (dataConPars, _) <- assert_ ("etaExpandVar, unrollPiWithNames:" <+>) $
    unrollPiWithNames appliedDataConType (map pName projs)
  dataConT <- con dataCon =<< mapM var (Ctx.vars dataConPars)
  let weakenBy = max 0 $ Ctx.length dataConPars - 1
  tel' <- Tel.subst 0 dataConT =<< Tel.weaken 1 weakenBy tel
  let telLen = Tel.length tel'
  dataConT' <- weaken_ telLen dataConT
  let sub = [Weaken (telLen+1) weakenBy, Substs [(telLen, dataConT')]]
  return (dataConPars Tel.++ tel', sub)

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
      Just t' <- lift $ strengthen_ 1 =<< app h (init elims)
      return t'
    Con dataCon args -> do
      DataCon tyCon _ _ _ <- lift $ getDefinition dataCon
      Constant (Record _ fields) _ <- lift $ getDefinition tyCon
      guard $ length args == length fields
      (t : ts) <- sequence (zipWith isRightProjection fields args)
      guard =<< (and <$> lift (mapM (termEq t) ts))
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

data InvertMetaVar t = InvertMetaVar
  { imvSubstitution :: [(Var, Term t)]
    -- ^ A substitution from variables in equated term to variables by
    -- the metavariable to terms in the context abstracted by the
    -- metavariable.
  , imvAbstractions :: Int
    -- ^ How many variables the metas abstracts.
  }

instance PrettyM InvertMetaVar where
  prettyM (InvertMetaVar x y) = prettyM $ InvertMeta x y

invertMetaVarVars :: InvertMetaVar t -> [Var]
invertMetaVarVars (InvertMetaVar sub _) = map fst sub

invertMetaVar
  :: forall t s a.
     (IsTerm t)
  => a -> (a -> Var -> TC t s (Either MetaVarSet a))
  -> Ctx t -> [Elim (Term t)]
  -> TC t s (TermTraverse' (a, Ctx t, [TermAction t], InvertMetaVar t))
invertMetaVar s act ctx elims = do
  let msg = do
        ctxDoc <- prettyM ctx
        elimsDoc <- prettyListM elims
        return $
          "ctx:" //> ctxDoc $$
          "elims:" //> elimsDoc
  debugBracket "invertMetaVar" msg $ runTermTraverseT $ do
    mvArgs <- TTT $ checkMetaVarElims elims
    (s', ctx', mvArgs', acts) <- TTT $ removeProjections s act ctx mvArgs
    lift $ whenDebug $ unless (null acts) $ do
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
          actsDoc <- prettyListM acts
          invDoc <- prettyM inv
          return $
            "ctx:" //> ctx'Doc $$
            "acts:" //> actsDoc $$
            "inversion:" //> invDoc
        return (s', ctx', acts, inv)

invertMetaVar_
  :: (IsTerm t)
  => Ctx t -> [Elim (Term t)]
  -> TC t s (TermTraverse' (Ctx t, [TermAction t], InvertMetaVar t))
invertMetaVar_ ctx elims = runTermTraverseT $ do
  ((), ctx', acts, inv) <-
    TTT $ invertMetaVar () (\() _ -> return (Right ())) ctx elims
  return (ctx', acts, inv)

mvaApplyActions
  :: (IsTerm t, MonadTerm t m) => [TermAction t] -> MetaVarArg' -> m MetaVarArg'
mvaApplyActions acts (MVAVar (v, ps)) = do
  vt <- var v
  vt' <- applyActions acts vt
  App (Var v') elims <- whnfView =<< eliminate vt' (map Proj ps)
  let Just ps' = mapM isProj elims
  return $ MVAVar (v', ps')
mvaApplyActions acts (MVARecord n args) = do
  MVARecord n <$> mapM (mvaApplyActions acts) args

varApplyActions
  :: (IsTerm t) => [TermAction t] -> Var -> TC t s (MetaVarArg Var)
varApplyActions acts v = do
  tView <- whnfView =<< (applyActions acts =<< var v)
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
  :: forall t s a. (IsTerm t)
  => a -> (a -> Var -> TC t s (Either MetaVarSet a))
  -> Ctx t -> [MetaVarArg']
  -> TC t s (TermTraverse' (a, Ctx t, [MetaVarArg Var], [TermAction t]))
removeProjections s0 act ctx0 mvArgs0 =
  either TTMetaVars TTOK <$> runExceptT (go s0 ctx0 mvArgs0)
  where
    go :: a -> Ctx t -> [MetaVarArg']
       -> ExceptT MetaVarSet (TC t s) (a, Ctx t, [MetaVarArg Var], [TermAction t])
    go s ctx [] = do
      return (s, ctx, [], [])
    go s ctx (MVAVar (v, []) : mvArgs) = do
      (s', ctx', mvArgs', tActs) <- go s ctx mvArgs
      mvArg <- lift $ varApplyActions tActs v
      return (s', ctx', mvArg : mvArgs', tActs)
    go s1 ctx1 (MVAVar (v, (p : ps)) : mvArgs) = do
      s2 <- ExceptT $ act s1 v
      Right (ctx2, tActs) <- lift $ etaExpandContextVar ctx1 v
      t <- lift $ (`eliminate` [Proj p]) =<< var v
      App (Var v') [] <- lift $ whnfView =<< applyActions tActs t
      mvArgs' <- lift $ mapM (mvaApplyActions tActs) mvArgs
      (s3, ctx3, mvArgs'', tActs') <- go s2 ctx2 (MVAVar (v', ps) : mvArgs')
      return (s3, ctx3, mvArgs'', tActs ++ tActs')
    go s1 ctx1 (MVARecord tyCon mvArgs1 : mvArgs2) = do
      (s2, ctx2, mvArgs1', tActs1) <- go s1 ctx1 mvArgs1
      (s3, ctx3, mvArgs2', tActs2) <- go s2 ctx2 mvArgs2
      return (s3, ctx3, MVARecord tyCon mvArgs1' : mvArgs2', tActs1 ++ tActs2)

-- | Returns an inversion if the pattern condition is respected for the
-- given 'MetaVarArg's.
checkPatternCondition
  :: forall t s. (IsTerm t)
  => [MetaVarArg Var] -> TC t s (Maybe (InvertMetaVar t))
checkPatternCondition mvArgs = do
  let allVs = concatMap toList mvArgs
  let linear = length allVs == Set.size (Set.fromList allVs)
  if linear
    then do
      vs <- mapM var $ reverse [V (Named "_" ix) | (ix, _) <- zip [0..] mvArgs]
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
  => InvertMetaVar t -> Term t
  -> TC t s (TermTraverse Var (Closed (Term t)))
applyInvertMetaVar (InvertMetaVar sub vsNum) =
  applyInvertMeta (InvertMeta sub vsNum)


-- Various
------------------------------------------------------------------------

-- | @killArgs α kills@ instantiates @α@ so that it discards the
--   arguments indicated by @kills@.
killArgs :: (IsTerm t) => MetaVar -> [Named Bool] -> TC t s (Closed (Term t))
killArgs newMv kills = do
  let vs = reverse [ V (Named n ix)
                   | (ix, Named n kill) <- zip [0..] (reverse kills), not kill
                   ]
  body <- metaVar newMv . map Apply =<< mapM var vs
  foldl' (\body' _ -> lam =<< body') (return body) kills

-- | If @t = α ts@ and @α : Δ -> D us@ where @D@ is some record type, it
-- will instantiate @α@ accordingly.
etaExpandMeta :: forall t s. (IsTerm t) => Term t -> TC t s (Term t)
etaExpandMeta t = do
  let fallback = do
        debug_ "didn't expand meta" ""
        return t
  debugBracket "etaExpandMeta" (prettyTermM t) $ do
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
  t <- etaExpandMeta t0
  let fallback = do
        debug_ "didn't expand" ""
        return t
  let expanded t' = do
        debug "expanded" $ prettyTermM t'
        return t'
  let msg = do
        typeDoc <- prettyTermM type_
        tDoc <- prettyTermM t
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
  appliedDataConType <- Tel.substs dataConTypeTel dataConType tyConArgs
  (dataConArgsCtx, _) <- unrollPi appliedDataConType
  dataConArgs <- createMvsPars ctxMvArgs $ Tel.tel dataConArgsCtx
  mvT <- Ctx.lam ctxMvArgs =<< con dataCon dataConArgs
  -- given the usage, here we know that the body is going to be well typed.
  -- TODO make sure that the above holds.
  instantiateMetaVar mv mvT
  return mvT

-- | @createMvsPars Γ Δ@ unrolls @Δ@ and creates a metavariable for
--   each of the elements.
createMvsPars
  :: (IsTerm t) => Ctx t -> Tel.Tel (Type t) -> TC t s [Term t]
createMvsPars _ Tel.Empty =
  return []
createMvsPars ctx (Tel.Cons (_, type') tel) = do
  mv  <- addMetaVarInCtx ctx type'
  mvs <- createMvsPars ctx =<< Tel.instantiate tel mv
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
  appliedProjType <- Tel.substs projTypeTel projType tyConArgs
  Pi _ endType <- whnfView appliedProjType
  endType' <- instantiate endType h
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
  sig <- askSignature
  case Sig.getDefinition sig dataCon of
    DataCon tyCon _ _ _ -> isRecordType tyCon
    _                   -> return False

isRecordType :: (IsTerm t) => Name -> TC t s Bool
isRecordType tyCon = do
  sig <- askSignature
  return $ case Sig.getDefinition sig tyCon of
    Constant (Record _ _) _ -> True
    _                       -> False
