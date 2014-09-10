{-# LANGUAGE OverloadedStrings #-}
module TypeCheck3.Solve
  ( SolveState
  , initSolveState
  , solve
  ) where

import           Prelude                          hiding (any)

import           Control.Monad.State.Strict       (get, put)
import           Control.Monad.Trans.Maybe        (MaybeT(MaybeT), runMaybeT)
import           Control.Monad.Trans.Writer.Strict
import qualified Data.HashSet                     as HS
import qualified Data.Set                         as Set
import           Syntax.Internal                  (Name, MetaVar)
import           Data.Monoid                      (Any(Any))

import           Prelude.Extended
import           PrettyPrint                      (($$), (<+>), (//>), (//), render, group, hang)
import qualified PrettyPrint                      as PP
import           Term
import           Term.Context                     (Ctx)
import qualified Term.Context                     as Ctx
import qualified Term.Signature                   as Sig
import qualified Term.Telescope                   as Tel
import           TypeCheck3.Common                hiding (Constraint(..), prettyConstraintTC)
import qualified TypeCheck3.Common                as Common
import           TypeCheck3.Monad

type SolveM t = TC t (SolveState t)

newtype SolveState t = SolveState {unSolveState :: Constraints t}

type BlockingMetas = HS.HashSet MetaVar
type Constraints t = [(BlockingMetas, Constraint t)]

data Constraint t
  = Unify (Ctx t) (Type t) (Term t) (Term t)
  | UnifySpine (Ctx t) (Type t) (Maybe (Term t)) [Elim (Term t)] [Elim (Term t)]
  | Conj [Constraint t]
  | (:>>:) (Constraint t) (Constraint t)

simplify :: Constraint t -> Maybe (Constraint t)
simplify (Conj [])    = Nothing
simplify (Conj cs)    = msum $ map simplify cs
simplify (c1 :>>: c2) = case simplify c1 of
                          Nothing  -> simplify c2
                          Just c1' -> Just (c1' :>>: c2)
simplify c            = Just c

instance Monoid (Constraint t) where
  mempty = Conj []

  Conj cs1 `mappend` Conj cs2 = Conj (cs1 ++ cs2)
  Conj cs1 `mappend` c2       = Conj (c2 : cs1)
  c1       `mappend` Conj cs2 = Conj (c1 : cs2)
  c1       `mappend` c2       = Conj [c1, c2]

constraint :: Common.Constraint t -> Constraint t
constraint (Common.Unify ctx type_ t1 t2) = Unify ctx type_ t1 t2
constraint (Common.Conj cs) = Conj $ map constraint $ concatMap flatten cs
  where
    flatten (Common.Conj constrs) = concatMap flatten constrs
    flatten c                     = [c]
constraint (c1 Common.:>>: c2) = constraint c1 :>>: constraint c2

sequenceConstraints :: Constraints t -> Constraint t -> Constraints t
sequenceConstraints scs1 c2 =
  let (css, cs1) = unzip scs1 in [(mconcat css, Conj cs1 :>>: c2)]

initSolveState :: SolveState t
initSolveState = SolveState []

solve :: forall t. (IsTerm t) => Common.Constraint t -> TC t (SolveState t) ()
solve c = do
  debugBracket_ "*** solve" $ do
    SolveState constrs0 <- get
    constrs <- go False [] ((mempty, constraint c) : constrs0)
    put $ SolveState constrs
  where
    go :: Bool -> Constraints t -> Constraints t -> TC t s (Constraints t)
    go progress constrs [] = do
      if progress
      then go False [] constrs
      else return constrs
    go progress newConstrs ((mvs, constr) : constrs) = do
      debug $ do
        let mvsDoc = PP.pretty $ HS.toList mvs
        constrDoc <- prettyConstraintTC constr
        return $
          "** Attempting" $$
          "constraint:" //> constrDoc $$
          "mvs:" //> mvsDoc
      attempt <- do mvsBodies <- forM (HS.toList mvs) getMetaVarBody
                    return $ null mvsBodies || any isJust mvsBodies
      if attempt
        then do
          constrs' <- solve' constr
          go True (constrs' ++ newConstrs) constrs
        else do
          go progress ((mvs, constr) : newConstrs) constrs

solve' :: (IsTerm t) => Constraint t -> TC t s (Constraints t)
solve' (Conj constrs) = do
  mconcat <$> forM constrs solve'
solve' (constr1 :>>: constr2) = do
  constrs1_0 <- solve' constr1
  let mbConstrs1 = mconcat [ fmap (\c -> [(mvs, c)]) (simplify constr)
                           | (mvs, constr) <- constrs1_0 ]
  case mbConstrs1 of
    Nothing -> do
      solve' constr2
    Just constrs1 -> do
      let (mvs, constr1') = mconcat constrs1
      return [(mvs, constr1' :>>: constr2)]
solve' (Unify ctx type_ t1 t2) = do
  checkEqual (ctx, type_, t1, t2)
solve' (UnifySpine ctx type_ mbH elims1 elims2) = do
  checkEqualSpine' ctx type_ mbH elims1 elims2

-- Equality
------------------------------------------------------------------------

type CheckEqual t = (Ctx t, Type t, Term t, Term t)

checkEqual
  :: (IsTerm t) => CheckEqual t -> TC t s (Constraints t)
checkEqual (ctx0, type0, t1_0, t2_0) = do
  let msg = do
        ctxDoc <- prettyContextTC ctx0
        typeDoc <- prettyTermTC type0
        xDoc <- prettyTermTC t1_0
        yDoc <- prettyTermTC t2_0
        return $
          "*** checkEqual" $$
          "ctx:" //> ctxDoc $$
          "type:" //> typeDoc $$
          "x:" //> xDoc $$
          "y:" //> yDoc
  debugBracket msg $ do
    runCheckEqual
      [checkSynEq, etaExpand, checkMetaVars]
      compareTerms
      (ctx0, type0, t1_0, t2_0)
  where
    runCheckEqual actions0 finally args = do
      case actions0 of
        []                 -> finally args
        (action : actions) -> do
          constrsOrArgs <- action args
          case constrsOrArgs of
            Left constrs -> return constrs
            Right args'  -> runCheckEqual actions finally args'

checkSynEq
  :: (IsTerm t)
  => CheckEqual t -> TC t s (Either (Constraints t) (CheckEqual t))
checkSynEq (ctx, type_, t1, t2) = do
  debugBracket_ "*** Syntactic check" $ do
    -- Optimization: try with a simple syntactic check first.
    t1' <- ignoreBlockingTC =<< whnfTC t1
    t2' <- ignoreBlockingTC =<< whnfTC t2
    -- TODO add option to skip this check
    eq <- termEqTC t1' t2'
    return $ if eq
      then Left []
      else Right (ctx, type_, t1', t2')

etaExpand
  :: (IsTerm t)
  => CheckEqual t -> TC t s (Either (Constraints t) (CheckEqual t))
etaExpand (ctx, type0, t1, t2) = do
  debugBracket_ "*** Eta expansion" $ do
    -- TODO compute expanding function once
    t1' <- expandOrDont "x" type0 t1
    t2' <- expandOrDont "y" type0 t2
    return $ Right (ctx, type0, t1', t2')
  where
    expandOrDont desc type_ t = do
      mbT <- expand type_ t
      case mbT of
        Nothing -> do
          debug_ $ "** Couldn't expand" <+> desc
          return t
        Just t' -> do
          debug $ do
            tDoc <- prettyTermTC t'
            return $
              "** Expanded" <+> desc <+> "to" //> tDoc
          return t'

    expand type_ t = do
      typeView <- whnfViewTC type_
      case typeView of
        App (Def tyCon) _ -> do
          tyConDef <- getDefinition tyCon
          case tyConDef of
            Constant (Record dataCon projs) _ -> do
              tView <- whnfViewTC t
              case tView of
                Con _ _ -> return Nothing
                _       -> do
                  ts <- mapM (\(n, ix) -> eliminateTC t [Proj n ix]) projs
                  Just <$> conTC dataCon ts
            _ ->
              return Nothing
        Pi _ codomain -> do
          name <- getAbsNameTC codomain
          v <- varTC $ boundVar name
          tView <- whnfViewTC t
          case tView of
            Lam _ -> return Nothing
            _     -> do t' <- liftTermM $ weaken_ 1 t
                        t'' <- lamTC =<< eliminateTC t' [Apply v]
                        return $ Just t''
        _ ->
          return Nothing

checkMetaVars
  :: (IsTerm t)
  => CheckEqual t -> TC t s (Either (Constraints t) (CheckEqual t))
checkMetaVars (ctx, type_, t1, t2) = do
  blockedT1 <- whnfTC t1
  t1' <- ignoreBlockingTC blockedT1
  blockedT2 <- whnfTC t2
  t2' <- ignoreBlockingTC blockedT2
  let syntacticEqualityOrPostpone mvs = do
        t1'' <- nfTC t1'
        t2'' <- nfTC t2'
        eq <- liftTermM $ termEq t1'' t2''
        if eq
          then return $ Left []
          else do
            debug_ $ "*** Both sides blocked, waiting for" <+> PP.pretty (HS.toList mvs)
            return $ Left [(mvs, Unify ctx type_ t1'' t2'')]
  case (blockedT1, blockedT2) of
    (MetaVarHead mv els1, MetaVarHead mv' els2) | mv == mv' -> do
      mbKills <- intersectVars els1 els2
      case mbKills of
        Nothing -> do
          syntacticEqualityOrPostpone $ HS.singleton mv
        Just kills -> do
          instantiateMetaVar mv =<< killArgs mv kills
          return (Left [])
    (MetaVarHead mv elims, _) -> do
      Left <$> metaAssign ctx type_ mv elims t2
    (_, MetaVarHead mv elims) -> do
      Left <$> metaAssign ctx type_ mv elims t1
    (BlockedOn mvs1 _ _, BlockedOn mvs2 _ _) -> do
      -- Both blocked, and we already checked for syntactic equality,
      -- let's try syntactic equality when normalized.
      syntacticEqualityOrPostpone (mvs1 <> mvs2)
    (BlockedOn mvs f elims, _) -> do
      Left <$> checkEqualBlockedOn ctx type_ mvs f elims t2
    (_, BlockedOn mvs f elims) -> do
      Left <$> checkEqualBlockedOn ctx type_ mvs f elims t1
    (NotBlocked _, NotBlocked _) -> do
      return $ Right (ctx, type_, t1', t2')

-- | @intersectVars us vs@ checks whether all relevant elements in @us@
--   and @vs@ are variables, and if yes, returns a prune list which says
--   @True@ for arguments which are different and can be pruned.
intersectVars :: (IsTerm t) => [Elim t] -> [Elim t] -> TC t s (Maybe [Named Bool])
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

killArgs :: (IsTerm t) => MetaVar -> [Named Bool] -> TC t s (Closed (Term t))
killArgs newMv kills = do
  let vs = reverse [ V (Named n ix)
                   | (ix, Named n kill) <- zip [0..] (reverse kills), not kill
                   ]
  body <- metaVarTC newMv . map Apply =<< mapM varTC vs
  foldl' (\body' _ -> lamTC =<< body') (return body) kills

checkEqualBlockedOn
  :: forall t s.
     (IsTerm t)
  => Ctx t -> Type t
  -> HS.HashSet MetaVar -> BlockedHead -> [Elim t]
  -> Term t
  -> TC t s (Constraints t)
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
                equalSpine (Def fun1) ctx elims1 elims2
              _ -> do
                t2Head <- termHead =<< unviewTC t2View
                case t2Head of
                  Nothing -> do
                    debug_ "** Definition invertible but we don't have a clause head."
                    fallback t1
                  Just tHead | Just (Clause pats _) <- lookup tHead injClauses -> do
                    debug_ $ "** Inverting on" <+> PP.pretty tHead
                    -- Make the eliminators match the patterns
                    matched <- matchPats pats elims1
                    -- And restart, if we matched something.
                    if matched
                      then do
                        debug_ $ "** Matched constructor, restarting"
                        checkEqual (ctx, type_, t1, t2)
                      else do
                        debug_ $ "** Couldn't match constructor"
                        fallback t1
                  Just _ -> do
                    checkError $ TermsNotEqual type_ t1 type_ t2
  where
    fallback t1 = return $ [(mvs, Unify ctx type_ t1 t2)]

    matchPats :: [Pattern] -> [Elim t] -> TC t s Bool
    matchPats (VarP : pats) (_ : elims) = do
      matchPats pats elims
    matchPats (ConP dataCon pats' : pats) (elim : elims) = do
      matched <- matchPat dataCon pats' elim
      (matched ||) <$> matchPats pats elims
    matchPats _ _ = do
      -- Less patterns than arguments is fine.
      --
      -- Less arguments than patterns is fine too -- it happens if we
      -- are waiting on some metavar which doesn't head an eliminator.
      return False

    matchPat :: Name -> [Pattern] -> Elim t -> TC t s Bool
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

equalSpine
  :: (IsTerm t)
  => Head -> Ctx t -> [Elim t] -> [Elim t] -> TC t s (Constraints t)
equalSpine h ctx elims1 elims2 = do
  hType <- headType ctx h
  checkEqualSpine ctx hType h elims1 elims2

checkEqualApplySpine
  :: (IsTerm t)
  => Ctx t -> Type t -> [Term t] -> [Term t]
  -> TC t s (Constraints t)
checkEqualApplySpine ctx type_ args1 args2 =
  checkEqualSpine' ctx type_ Nothing (map Apply args1) (map Apply args2)

checkEqualSpine
  :: (IsTerm t)
  => Ctx t -> Type t -> Head -> [Elim (Term t)] -> [Elim (Term t)]
  -> TC t s (Constraints t)
checkEqualSpine ctx type_ h elims1 elims2  = do
  h' <- appTC h []
  checkEqualSpine' ctx type_ (Just h') elims1 elims2

checkEqualSpine'
  :: (IsTerm t)
  => Ctx t -> Type t -> Maybe (Term t)
  -> [Elim (Term t)] -> [Elim (Term t)]
  -> TC t s (Constraints t)
checkEqualSpine' _ _ _ [] [] = do
  return []
checkEqualSpine' ctx type_ mbH (elim1 : elims1) (elim2 : elims2) = do
  let msg = do
        let prettyMbH mbH = case mbH of
              Nothing -> return "No head"
              Just h  -> prettyTermTC h
        typeDoc <- prettyTermTC type_
        hDoc <- prettyMbH mbH
        elims1Doc <- prettyElimsTC $ elim1 : elims1
        elims2Doc <- prettyElimsTC $ elim2 : elims2
        return $
          "*** checkEqualSpine" $$
          "type:" //> typeDoc $$
          "head:" //> hDoc $$
          "elims1:" //> elims1Doc $$
          "elims2:" //> elims2Doc
  debugBracket msg $ do
    case (elim1, elim2) of
      (Apply arg1, Apply arg2) -> do
        Pi dom cod <- whnfViewTC type_
        res1 <- checkEqual (ctx, dom, arg1, arg2)
        mbCod <- liftTermM $ strengthen_ 1 cod
        mbH' <- traverse (`eliminateTC` [Apply arg1]) mbH
        -- If the rest is non-dependent, we can continue immediately.
        case mbCod of
          Nothing -> do
            cod' <- liftTermM $ instantiate cod arg1
            return $ sequenceConstraints res1 (UnifySpine ctx cod' mbH' elims1 elims2)
          Just cod' -> do
            res2 <- checkEqualSpine' ctx cod' mbH' elims1 elims2
            return (res1 <> res2)
      (Proj proj projIx, Proj proj' projIx') | proj == proj' && projIx == projIx' -> do
          let Just h = mbH
          (h', type') <- applyProjection proj h type_
          checkEqualSpine' ctx type' (Just h') elims1 elims2
      _ ->
        checkError $ SpineNotEqual type_ (elim1 : elims1) type_ (elim1 : elims2)
checkEqualSpine' _ type_ _ elims1 elims2 = do
  checkError $ SpineNotEqual type_ elims1 type_ elims2

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

metaAssign
  :: (IsTerm t)
  => Ctx t -> Type t -> MetaVar -> [Elim (Term t)] -> Term t
  -> TC t s (Constraints t)
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
          checkEqual (ctx0, type0, mvT', t0)
      Nothing -> do
        (ctx, elims, sub) <- etaExpandVars ctx0 elims0
        debug $ do
          -- TODO this check could be more precise
          if Ctx.length ctx0 == Ctx.length ctx
          then return "** No change in context"
          else do
            ctxDoc <- prettyContextTC ctx
            return $ "** New context:" //> ctxDoc
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
                return [(mvs, Unify ctx type_ mvT t)]
              Just mvT -> do
                mvT' <- eliminateTC mvT elims'
                checkEqual (ctx, type_, mvT', t')
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
                instantiateMetaVar mv t'
                return []
              TTMetaVars mvs -> do
                debug_ ("** Inversion blocked on" //> PP.pretty (HS.toList mvs))
                mvT <- metaVarTC mv elims
                return [(mvs, Unify ctx type_ mvT t)]
              TTFail v ->
                checkError $ FreeVariableInEquatedTerm mv elims t v

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
          error "impossible.createNewMeta: metavar type too short"
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

-- | Eliminates projected variables by eta-expansion, thus modifying the
-- context.
etaExpandVars
  :: (IsTerm t)
  => Ctx t
  -- ^ Context we're in
  -> [Elim t]
  -- ^ Eliminators on the MetaVar
  -> TC t s (Ctx t, [Elim t], t -> TermM t)
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
  -> TC t s (Tel.Tel t, t -> TermM t)
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
  :: (IsTerm t) => [Elim t] -> TC t s (Maybe (Var, Name))
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

compareTerms :: (IsTerm t) => CheckEqual t -> TC t s (Constraints t)
compareTerms (ctx, type_, t1, t2) = do
  typeView <- whnfViewTC type_
  t1View <- whnfViewTC t1
  t2View <- whnfViewTC t2
  let mkVar n ix = varTC $ V $ named n ix
  case (typeView, t1View, t2View) of
    -- Note that here we rely on canonical terms to have canonical
    -- types, and on the terms to be eta-expanded.
    (Pi dom cod, Lam body1, Lam body2) -> do
      -- TODO there is a bit of duplication between here and expansion.
      name <- getAbsNameTC body1
      ctx' <- extendContext ctx (name, dom)
      checkEqual (ctx', cod, body1, body2)
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
      return []
    ( App (Def _) tyConPars0, Con dataCon dataConArgs1, Con dataCon' dataConArgs2) | dataCon == dataCon' -> do
       let Just tyConPars = mapM isApply tyConPars0
       DataCon _ dataConTypeTel dataConType <- getDefinition dataCon
       appliedDataConType <- liftTermM $ Tel.substs dataConTypeTel dataConType tyConPars
       checkEqualApplySpine ctx appliedDataConType dataConArgs1 dataConArgs2
    (Set, Set, Set) -> do
      return []
    (_, App h elims1, App h' elims2) | h == h' -> do
      equalSpine h ctx elims1 elims2
    (_, _, _) -> do
     checkError $ TermsNotEqual type_ t1 type_ t2


-- Pretty printing Constraints

prettyConstraintTC
  :: (IsTerm t) => Constraint t -> TC t s PP.Doc
prettyConstraintTC c = case c of
  Unify ctx type_ t1 t2 -> do
    ctxDoc <- prettyContextTC ctx
    typeDoc <- prettyTermTC type_
    t1Doc <- prettyTermTC t1
    t2Doc <- prettyTermTC t2
    return $ group $
      ctxDoc <+> "|-" //
      group (t1Doc // hang 2 "=" // t2Doc // hang 2 ":" // typeDoc)
  c1 :>>: c2 -> do
    c1Doc <- prettyConstraintTC c1
    c2Doc <- prettyConstraintTC c2
    return $ group (group c1Doc $$ hang 2 ">>" $$ group c2Doc)
  Conj cs -> do
    csDoc <- mapM prettyConstraintTC cs
    return $
      "Conj" //> PP.list csDoc
  UnifySpine ctx type_ mbH elims1 elims2 -> do
    ctxDoc <- prettyContextTC ctx
    typeDoc <- prettyTermTC type_
    hDoc <- case mbH of
      Nothing -> return "no head"
      Just h  -> prettyTermTC h
    elims1Doc <- prettyElimsTC elims1
    elims2Doc <- prettyElimsTC elims2
    return $
      "UnifySpine" $$
      "ctx:" //> ctxDoc $$
      "type:" //> typeDoc $$
      "h:" //> hDoc $$
      "elims1:" //> elims1Doc $$
      "elims2:" //> elims1Doc
