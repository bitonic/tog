{-# LANGUAGE OverloadedStrings #-}
module TypeCheck3.Solve.TwoContexts
  ( SolveState
  , initSolveState
  , solve
  ) where

import           Prelude                          hiding (any, pi)

import           Control.Monad.State.Strict       (get, put)
import           Control.Monad.Trans.Maybe        (runMaybeT)
import           Control.Monad.Trans.Writer.Strict (execWriterT, tell)
import qualified Data.HashSet                     as HS
import qualified Data.Set                         as Set
import           Syntax.Internal                  (Name)

import           Conf
import           Prelude.Extended
import           PrettyPrint                      (($$), (<+>), (//>), (//), group, hang)
import qualified PrettyPrint                      as PP
import           Term
import           Term.Context                     (Ctx)
import qualified Term.Context                     as Ctx
import qualified Term.Telescope                   as Tel
import qualified TypeCheck3.Common                as Common
import           TypeCheck3.Common                hiding (Constraint(..), Constraints)
import qualified TypeCheck3.Check                 as Check
import           TypeCheck3.Monad
import           TypeCheck3.Solve.Common

-- These definitions should be in every Solve module
----------------------------------------------------

newtype SolveState t = SolveState (Constraints t)

type BlockingMetas = HS.HashSet MetaVar
type Constraints t = [(BlockingMetas, Constraint t)]

data Constraint t
  = Unify (Ctx t) (Type t) (Term t) (Ctx t) (Type t) (Term t)
  | UnifySpine (Ctx t) (Type t) (Maybe (Term t)) [Elim (Term t)]
               (Ctx t) (Type t) (Maybe (Term t)) [Elim (Term t)]
  | CheckAndInstantiate (Type t) (Term t) MetaVar

constraints :: (IsTerm t) => Common.Constraint t -> [Constraint t]
constraints (Common.JMEq ctx type1 t1 type2 t2) =
  [Unify ctx set type1 ctx set type2, Unify ctx type1 t1 ctx type2 t2]

initSolveState :: SolveState t
initSolveState = SolveState []

solve :: forall t. (IsTerm t) => Common.Constraint t -> TC t (SolveState t) ()
solve c = do
  debugBracket_ "*** solve" $ do
    SolveState constrs0 <- get
    constrs <- go False [] (map (mempty,) (constraints c) ++ constrs0)
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
        constrDoc <- prettyM constr
        return $
          "** Attempting" $$
          "constraint:" //> constrDoc $$
          "mvs:" //> mvsDoc
      attempt <- do mvsBodies <- forM (HS.toList mvs) getMetaVarBody
                    return $ null mvsBodies || any isJust mvsBodies
      if attempt
        then do
          constrs' <- solveConstraint constr
          go True (constrs' ++ newConstrs) constrs
        else do
          go progress ((mvs, constr) : newConstrs) constrs

solveConstraint :: (IsTerm t) => Constraint t -> TC t s (Constraints t)
solveConstraint constr0 = do
  let msg = do
        constrDoc <- prettyM constr0
        return $
          "*** solveConstraint" $$
          "constraint:" //> constrDoc
  debugBracket msg $ do
    case constr0 of
      Unify ctx1 type1 t1 ctx2 type2 t2 -> do
        checkEqual (ctx1, type1, t1, ctx2, type2, t2)
      UnifySpine ctx1 type1 mbH1 elims1 ctx2 type2 mbH2 elims2 -> do
        checkEqualSpine' ctx1 type1 mbH1 elims1 ctx2 type2 mbH2 elims2
      CheckAndInstantiate type_ term mv -> do
        checkAndInstantiate type_ term mv

instance PrettyM SolveState where
  prettyM (SolveState cs0) = do
     detailed <- confProblemsReport <$> readConf
     let go cs = do
           tell $ "-- Unsolved problems:" <+> PP.pretty (length cs)
           when detailed $ forM_ cs $ \(mvs, c) -> do
             tell $ PP.line <> "------------------------------------------------------------------------"
             cDoc <- lift $ prettyM c
             tell $ PP.line <> "** Waiting on" <+> PP.pretty (HS.toList mvs) $$ cDoc
     execWriterT $ go cs0

-- This is local stuff
----------------------

-- Equality
------------------------------------------------------------------------

type CheckEqual t = (Ctx t, Type t, Term t, Ctx t, Type t, Term t)

data CheckEqualProgress t
  = Done (Constraints t)
  | KeepGoing (CheckEqual t)

done :: Constraints t -> TC t s (CheckEqualProgress t)
done = return . Done

keepGoing :: CheckEqual t -> TC t s (CheckEqualProgress t)
keepGoing = return . KeepGoing

checkEqual
  :: (IsTerm t) => CheckEqual t -> TC t s (Constraints t)
checkEqual (ctx1_0, type1_0, t1_0, ctx2_0, type2_0, t2_0) = do
  let msg = do
        ctxXDoc <- prettyM ctx1_0
        typeXDoc <- prettyTermM type1_0
        xDoc <- prettyTermM t1_0
        ctxYDoc <- prettyM ctx2_0
        typeYDoc <- prettyTermM type2_0
        yDoc <- prettyTermM t2_0
        return $
          "*** checkEqual" $$
          "ctxX:" //> ctxXDoc $$
          "typeX:" //> typeXDoc $$
          "x:" //> xDoc $$
          "ctxY:" //> ctxYDoc $$
          "typeY:" //> typeYDoc $$
          "y:" //> yDoc
  debugBracket msg $ do
    runCheckEqual
      [ checkTypeHeads          -- Check that the types are both non-blocked
      , checkSynEq              -- Optimization: check if the two terms are equal
      , etaExpandContexts       -- Expand all record types things in the context
      , etaExpand               -- Eta expand the terms
      , unrollMetaVarsArgs      -- Removes record-type arguments from metas
      , etaExpandMetaVars       -- Expand the term if they're metas
      , checkMetaVars           -- Assign/intersect metavariables if needed
      ]
      compareTerms
      (ctx1_0, type1_0, t1_0, ctx2_0, type2_0, t2_0)
  where
    runCheckEqual actions0 finally args = do
      case actions0 of
        []                 -> finally args
        (action : actions) -> do
          constrsOrArgs <- action args
          case constrsOrArgs of
            Done constrs    -> return constrs
            KeepGoing args' -> runCheckEqual actions finally args'

-- | Before proceeding, we need to make sure that both types are
-- non-blocking, so that we can perform eta-expansion & co. reliably.
checkTypeHeads
  :: (IsTerm t)
  => CheckEqual t -> TC t s (CheckEqualProgress t)
checkTypeHeads args@(ctx1, type1, t1, ctx2, type2, t2) = do
  blockedType1 <- whnf type1
  blockedType2 <- whnf type2
  case isBlocked blockedType1 <> isBlocked blockedType2 of
    Nothing  -> keepGoing args
    Just mvs -> done [(mvs, Unify ctx1 type1 t1 ctx2 type2 t2)]

checkSynEq
  :: (IsTerm t)
  => CheckEqual t -> TC t s (CheckEqualProgress t)
checkSynEq args@(ctx1, type1, t1, ctx2, type2, t2) = do
  disabled <- confDisableSynEquality <$> readConf
  if disabled
    then do
      keepGoing args
    else do
      debugBracket_ "*** Syntactic check" $ do
        -- Optimization: try with a simple syntactic check first.
        t1' <- ignoreBlocking =<< whnf t1
        t2' <- ignoreBlocking =<< whnf t2
        -- TODO add option to skip this check
        eq <- termEq t1' t2'
        if eq
          then done []
          else keepGoing (ctx1, type1, t1', ctx2, type2, t2')

etaExpandContexts
  :: forall t s. (IsTerm t)
  => CheckEqual t -> TC t s (CheckEqualProgress t)
etaExpandContexts (ctx1_0, type1_0, t1_0, ctx2_0, type2_0, t2_0) = do
  debugBracket_ "*** Eta-expanding context" $ do
    (tel1, type1, t1, tel2, type2, t2) <-
      go (Tel.tel ctx1_0) type1_0 t1_0 (Tel.tel ctx2_0) type2_0 t2_0
    debug $ do
      if (Tel.length tel1 /= Ctx.length ctx1_0)
        then do
          ctx1Doc <- prettyM ctx1_0
          tel1Doc <- prettyM tel1
          ctx2Doc <- prettyM ctx2_0
          tel2Doc <- prettyM tel2
          return $
            "** Expanded" $$
            "before1" //> ctx1Doc $$
            "after1" //> tel1Doc $$
            "before2" //> ctx2Doc $$
            "after2" //> tel2Doc
        else do
          return "** No change"
    keepGoing (Tel.unTel tel1, type1, t1, Tel.unTel tel2, type2, t2)
  where
    go Tel.Empty type1 t1 Tel.Empty type2 t2 = do
      return (Tel.Empty, type1, t1, Tel.Empty, type2, t2)
    go (Tel.Cons (n1, arg1) tel1) type1 t1 (Tel.Cons (n2, arg2) tel2) type2 t2 = do
      -- Check if both types are record types.
      mbTyCon <- runMaybeT $ do
        App (Def tyCon) tyConArgs1 <- lift $ whnfView arg1
        True <- lift $ isRecordType tyCon
        let Just tyConPars1 = mapM isApply tyConArgs1
        App (Def tyCon') tyConArgs2 <- lift $ whnfView arg2
        let Just tyConPars2 = mapM isApply tyConArgs2
        unless (tyCon == tyCon') $
          lift $ fatalError "etaExpandContexts: different tycons"
        return (tyCon, tyConPars1, tyConPars2)
      -- If the are not, then continue through the rest of the
      -- context.  If they are, split up the variable into the record
      -- fields.
      case mbTyCon of
        Nothing -> do
          (tel1', type1', t1', tel2', type2', t2') <- go tel1 type1 t1 tel2 type2 t2
          return ( Tel.Cons (n1, arg1) tel1', type1', t1',
                   Tel.Cons (n2, arg2) tel2', type2', t2'
                 )
        Just (tyCon, tyConPars1, tyConPars2) -> do
          Constant (Record dataCon projs) _ <- getDefinition tyCon
          DataCon _ _ dataConTypeTel dataConType <- getDefinition dataCon
          -- Instantiate the tycon pars in the type of the datacon
          appliedDataConType1 <- Tel.substs dataConTypeTel dataConType tyConPars1
          appliedDataConType2 <- Tel.substs dataConTypeTel dataConType tyConPars2
          let unrollDataConType t =
                assert ("etaExpandVar, unrollPiWithNames:" <+>) $
                unrollPiWithNames t (map pName projs)
          -- Get the type of each field
          (dataConPars1, _) <- unrollDataConType appliedDataConType1
          (dataConPars2, _) <- unrollDataConType appliedDataConType2
          let numDataConPars = Ctx.length dataConPars1
          -- Build a term with variables representing the fields
          recordTerm1 <- con dataCon =<< mapM var (Ctx.vars dataConPars1)
          recordTerm2 <- con dataCon =<< mapM var (Ctx.vars dataConPars2)
          -- Now we need a telescope with the fields, and then the
          -- telescope that we already had, but with the variable that
          -- stood for arg replaced with the record term.
          --
          -- Note that the telescopes also need to be weakened,
          -- since we're introducing new variables.
          let telLen = Tel.length tel1
          let weakenBy = max 0 $ numDataConPars-1
          let adjustTel t x = Tel.subst 0 t =<< Tel.weaken 1 weakenBy x
          tel1' <- adjustTel recordTerm1 tel1
          tel2' <- adjustTel recordTerm1 tel2
          let adjustTerm t x = do
                t' <- weaken_ telLen t
                subst telLen t' =<< weaken (telLen+1) weakenBy x
          t1' <- adjustTerm recordTerm1 t1
          type1' <- adjustTerm recordTerm1 type1
          t2' <- adjustTerm recordTerm2 t2
          type2' <- adjustTerm recordTerm2 type2
          -- Now continue.
          go (dataConPars1 Tel.++ tel1') type1' t1'
             (dataConPars1 Tel.++ tel2') type2' t2'
    go _ _ _ _ _ _ = do
      fatalError "etaExpandContext: different lengthts"

etaExpandMetaVars
  :: (IsTerm t)
  => CheckEqual t -> TC t s (CheckEqualProgress t)
etaExpandMetaVars (ctx1, type1, t1, ctx2, type2, t2) = do
  -- Try to eta-expand the metavariable first.  We do this before
  -- expanding the terms because if we expand the terms first we might
  -- "lose" some metavariables.  Consider the case where we have `α :
  -- Unit'.  This would get expanded to `tt : Unit', but then we don't
  -- instantiate `α' to `tt'.
  t1' <- fromMaybe t1 <$> etaExpandMetaVar t1
  t2' <- fromMaybe t2 <$> etaExpandMetaVar t2
  keepGoing (ctx1, type1, t1', ctx2, type2, t2')

unrollMetaVarsArgs
  :: (IsTerm t)
  => CheckEqual t -> TC t s (CheckEqualProgress t)
unrollMetaVarsArgs (ctx1, type1, t1, ctx2, type2, t2) = do
  t1' <- fromMaybe t1 <$> unrollMetaVarArgs t1
  t2' <- fromMaybe t2 <$> unrollMetaVarArgs t2
  keepGoing (ctx1, type1, t1', ctx2, type2, t2')

etaExpand
  :: (IsTerm t)
  => CheckEqual t -> TC t s (CheckEqualProgress t)
etaExpand (ctx1, type1, t1, ctx2, type2, t2) = do
  debugBracket_ "*** Eta expansion" $ do
    t1' <- expandOrDont "x" type1 t1
    t2' <- expandOrDont "y" type2 t2
    keepGoing (ctx1, type1, t1', ctx2, type2, t2')
  where
    expandOrDont desc type_ t = do
      mbT <- expand type_ t
      case mbT of
        Nothing -> do
          debug_ $ "** Couldn't expand" <+> desc
          return t
        Just t' -> do
          debug $ do
            tDoc <- prettyTermM t'
            return $
              "** Expanded" <+> desc <+> "to" //> tDoc
          return t'

    expand type_ t = do
      typeView <- whnfView type_
      case typeView of
        App (Def tyCon) _ -> do
          tyConDef <- getDefinition tyCon
          case tyConDef of
            Constant (Record dataCon projs) _ -> do
              tView <- whnfView t
              case tView of
                Con _ _ -> return Nothing
                _       -> do
                  ts <- mapM (\p -> eliminate t [Proj p]) projs
                  Just <$> con dataCon ts
            _ ->
              return Nothing
        Pi _ codomain -> do
          name <- getAbsName_ codomain
          v <- var $ boundVar name
          tView <- whnfView t
          case tView of
            Lam _ -> return Nothing
            _     -> do t' <- weaken_ 1 t
                        t'' <- lam =<< eliminate t' [Apply v]
                        return $ Just t''
        _ ->
          return Nothing

checkAndInstantiate
  :: (IsTerm t)
  => Closed (Type t) -> Closed (Term t) -> MetaVar
  -> TC t s (Constraints t)
checkAndInstantiate type_ term mv = do
  let msg = do
        typeDoc <- prettyTermM type_
        termDoc <- prettyTermM term
        return $
          "*** checkAndInstantiate" $$
          "type:" //> typeDoc $$
          "term:" //> termDoc $$
          "metavar:" //> PP.pretty mv
  debugBracket msg $ do
    mbErr <- catchTC $ Check.check Ctx.Empty term type_
    case mbErr of
      Left _err -> do
        mvs1 <- metaVars type_
        mvs2 <- metaVars term
        let mvs = mvs1 <> mvs2
        debug_ $ "** Could not typecheck, waiting on:" <+> PP.pretty (HS.toList mvs)
        when (HS.null mvs) $
          fatalError $ "checkAndInstantiate: no metas!"
        return [(mvs, CheckAndInstantiate type_ term mv)]
      Right () -> do
        instantiateMetaVar mv term
        return []

checkedInstantiateMetaVar
  :: (IsTerm t)
  => MetaVar -> Closed (Term t) -> TC t s (Constraints t)
checkedInstantiateMetaVar mv mvT = do
  mvType <- getMetaVarType mv
  checkAndInstantiate mvType mvT mv

checkMetaVars
  :: forall t s. (IsTerm t)
  => CheckEqual t -> TC t s (CheckEqualProgress t)
checkMetaVars (ctx1, type1, t1, ctx2, type2, t2) = do
  blockedT1 <- whnf t1
  t1' <- ignoreBlocking blockedT1
  blockedT2 <- whnf t2
  t2' <- ignoreBlocking blockedT2
  let syntacticEqualityOrPostpone mvs = do
        t1'' <- nf t1'
        t2'' <- nf t2'
        eq <- termEq t1'' t2''
        if eq
          then done []
          else do
            debug_ $ "*** Both sides blocked, waiting for" <+> PP.pretty (HS.toList mvs)
            done [(mvs, Unify ctx1 type1 t1'' ctx2 type2 t2'')]
  case (blockedT1, blockedT2) of
    (MetaVarHead mv els1, MetaVarHead mv' els2) | mv == mv' -> do
      mbKills <- intersectVars els1 els2
      case mbKills of
        Nothing -> do
          syntacticEqualityOrPostpone $ HS.singleton mv
        Just kills -> do
          Done <$> (checkedInstantiateMetaVar mv =<< killArgs mv kills)
    (MetaVarHead mv elims, _) -> do
      metaAssign ctx1 type1 mv elims ctx2 type2 t2
    (_, MetaVarHead mv elims) -> do
      metaAssign ctx2 type2 mv elims ctx1 type1 t1
    (BlockedOn mvs1 _ _, BlockedOn mvs2 _ _) -> do
      -- Both blocked, and we already checked for syntactic equality,
      -- let's try syntactic equality when normalized.
      syntacticEqualityOrPostpone (mvs1 <> mvs2)
    (BlockedOn mvs f elims, _) -> do
      Done <$> checkEqualBlockedOn ctx1 type1 mvs f elims ctx2 type2 t2
    (_, BlockedOn mvs f elims) -> do
      Done <$> checkEqualBlockedOn ctx2 type2 mvs f elims ctx1 type1 t1
    (NotBlocked _, NotBlocked _) -> do
      keepGoing (ctx1, type1, t1', ctx2, type2, t2')

checkEqualBlockedOn
  :: forall t s.
     (IsTerm t)
  => Ctx t -> Type t -> HS.HashSet MetaVar -> BlockedHead -> [Elim t]
  -> Ctx t -> Type t -> Term t
  -> TC t s (Constraints t)
checkEqualBlockedOn ctx1 type1 mvs bh elims1 ctx2 type2 t2 = do
  let msg = "*** Equality blocked on metavars" <+> PP.pretty (HS.toList mvs) PP.<>
            ", trying to invert definition" <+> PP.pretty bh
  t1 <- ignoreBlocking $ BlockedOn mvs bh elims1
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
            t2View <- whnfView t2
            case t2View of
              App (Def fun2) elims2 | fun1 == fun2 -> do
                debug_ "** Could invert, and same heads, checking spines."
                equalSpine (Def fun1) ctx1 elims1 ctx2 elims2
              _ -> do
                t2Head <- termHead =<< unview t2View
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
                        checkEqual (ctx1, type1, t1, ctx2, type2, t2)
                      else do
                        debug_ $ "** Couldn't match constructor"
                        fallback t1
                  Just _ -> do
                    checkError $ TermsNotEqual type1 t1 type2 t2
  where
    fallback t1 = return $ [(mvs, Unify ctx1 type1 t1 ctx2 type2 t2)]

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
      tView <- whnfView t
      case tView of
        App (Meta mv) mvArgs -> do
          mvT <- instantiateDataCon mv dataCon
          void $ matchPat dataCon pats . Apply =<< eliminate mvT mvArgs
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

equalSpine
  :: (IsTerm t)
  => Head -> Ctx t -> [Elim t] -> Ctx t -> [Elim t]
  -> TC t s (Constraints t)
equalSpine h ctx1 elims1 ctx2 elims2 = do
  h1Type <- headType ctx1 h
  h2Type <- headType ctx2 h
  checkEqualSpine ctx1 h1Type h elims1 ctx2 h2Type h elims2

checkEqualApplySpine
  :: (IsTerm t)
  => Ctx t -> Type t -> [Term t]
  -> Ctx t -> Type t -> [Term t]
  -> TC t s (Constraints t)
checkEqualApplySpine ctx1 type1 args1 ctx2 type2 args2 =
  checkEqualSpine' ctx1 type1 Nothing (map Apply args1) ctx2 type2 Nothing (map Apply args2)

checkEqualSpine
  :: (IsTerm t)
  => Ctx t -> Type t -> Head -> [Elim (Term t)]
  -> Ctx t -> Type t -> Head -> [Elim (Term t)]
  -> TC t s (Constraints t)
checkEqualSpine ctx1 type1 h1 elims1 ctx2 type2 h2 elims2  = do
  h1' <- app h1 []
  h2' <- app h2 []
  checkEqualSpine' ctx1 type1 (Just h1') elims1 ctx2 type2 (Just h2') elims2

checkEqualSpine'
  :: (IsTerm t)
  => Ctx t -> Type t -> Maybe (Term t) -> [Elim (Term t)]
  -> Ctx t -> Type t -> Maybe (Term t) -> [Elim (Term t)]
  -> TC t s (Constraints t)
checkEqualSpine' _ _ _ [] _ _ _ [] = do
  return []
checkEqualSpine' ctx1 type1 mbH1 (elim1 : elims1) ctx2 type2 mbH2 (elim2 : elims2) = do
  let msg = do
        let prettyMbH mbH = case mbH of
              Nothing -> return "No head"
              Just h  -> prettyTermM h
        type1Doc <- prettyTermM type1
        h1Doc <- prettyMbH mbH1
        elims1Doc <- prettyListM $ elim1 : elims1
        type2Doc <- prettyTermM type2
        h2Doc <- prettyMbH mbH2
        elims2Doc <- prettyListM $ elim2 : elims2
        return $
          "*** checkEqualSpine" $$
          "type1:" //> type1Doc $$
          "head1:" //> h1Doc $$
          "elims1:" //> elims1Doc $$
          "type2:" //> type2Doc $$
          "head2:" //> h2Doc $$
          "elims2:" //> elims2Doc
  debugBracket msg $ do
    case (elim1, elim2) of
      (Apply arg1, Apply arg2) -> do
        Pi dom1 cod1 <- whnfView type1
        Pi dom2 cod2 <- whnfView type2
        res1  <- checkEqual (ctx1, dom1, arg1, ctx2, dom2, arg2)
        cod1' <- instantiate cod1 arg1
        mbH1' <- traverse (`eliminate` [Apply arg1]) mbH1
        cod2' <- instantiate cod2 arg2
        mbH2' <- traverse (`eliminate` [Apply arg2]) mbH2
        res2  <- checkEqualSpine' ctx1 cod1' mbH1' elims1 ctx2 cod2' mbH2' elims2
        return $ res1 ++ res2
      (Proj proj, Proj proj') | proj == proj' -> do
          let Just h1 = mbH1
          (h1', type1') <- applyProjection proj h1 type1
          let Just h2 = mbH2
          (h2', type2') <- applyProjection proj h2 type2
          checkEqualSpine' ctx1 type1' (Just h1') elims1 ctx2 type2' (Just h2') elims2
      _ ->
        checkError $ SpineNotEqual type1 (elim1 : elims1) type2 (elim1 : elims2)
checkEqualSpine' _ type1 _ elims1 _ type2 _ elims2 = do
  checkError $ SpineNotEqual type1 elims1 type2 elims2

metaAssign
  :: (IsTerm t)
  => Ctx t -> Type t -> MetaVar -> [Elim (Term t)]
  -> Ctx t -> Type t -> Term t
  -> TC t s (CheckEqualProgress t)
metaAssign ctx1 type1 mv elims1 ctx2 type2 t2 = do
  mvType <- getMetaVarType mv
  let msg = do
        mvTypeDoc <- prettyTermM mvType
        elimsDoc <- prettyListM elims1
        tDoc <- prettyTermM t2
        return $
          "*** metaAssign" $$
          "assigning metavar:" <+> PP.pretty mv $$
          "of type:" //> mvTypeDoc $$
          "elims:" //> elimsDoc $$
          "to term:" //> tDoc
  debugBracket msg $ do
    -- See if we can invert the metavariable
    ttInv <- invertMeta elims1
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
        t2' <- nf t2
        -- TODO should we really prune allowing all variables here?  Or
        -- only the rigid ones?
        fvs <- fvAll <$> freeVars t2'
        elims1' <- mapM nf' elims1
        mbMvT <- prune fvs mv elims1'
        -- If we managed to prune them, restart the equality.
        -- Otherwise, wait on the metavariables.
        case mbMvT of
          Nothing -> do
            mvT <- metaVar mv elims1'
            done [(mvs, Unify ctx1 type1 mvT ctx2 type2 t2')]
          Just mvT -> do
            mvT' <- eliminate mvT elims1'
            done =<< checkEqual (ctx1, type1, mvT', ctx2, type2, t2')
      Right inv -> do
        debug $ do
          invDoc <- prettyM inv
          return $
            "** Could invert, now pruning" $$
            "inversion:" //> invDoc
        t2_1 <- pruneTerm (Set.fromList $ invertMetaVars inv) t2
        debug $ do
          t1Doc <- prettyTermM t2_1
          return $ "** Pruned term:" //> t1Doc
        t2_2 <- applyInvertMeta inv t2_1
        case t2_2 of
          TTOK t2' -> do
            mvs <- metaVars t2'
            when (mv `HS.member` mvs) $
              checkError $ OccursCheckFailed mv t2'
            Done <$> checkedInstantiateMetaVar mv t2'
          TTMetaVars mvs -> do
            debug_ ("** Inversion blocked on" //> PP.pretty (HS.toList mvs))
            mvT <- metaVar mv elims1
            done [(mvs, Unify ctx1 type1 mvT ctx2 type2 t2)]
          TTFail v ->
            checkError $ FreeVariableInEquatedTerm mv elims1 t2 v

compareTerms :: (IsTerm t) => CheckEqual t -> TC t s (Constraints t)
compareTerms (ctx1, type1, t1, ctx2, type2, t2) = do
  type1View <- whnfView type1
  t1View <- whnfView t1
  type2View <- whnfView type2
  t2View <- whnfView t2
  let mkVar n ix = var $ V $ named n ix
  case (type1View, t1View, type2View, t2View) of
    -- Note that here we rely on canonical terms to have canonical
    -- types, and on the terms to be eta-expanded.
    (Pi dom1 cod1, Lam body1, Pi dom2 cod2, Lam body2) -> do
      -- TODO there is a bit of duplication between here and expansion.
      name1 <- getAbsName_ body1
      name2 <- getAbsName_ body2
      ctx1' <- extendContext ctx1 (name1, dom1)
      ctx2' <- extendContext ctx2 (name2, dom2)
      checkEqual (ctx1', cod1, body1, ctx2', cod2, body2)
    (Set, Pi dom1 cod1, Set, Pi dom2 cod2) -> do
      -- Pi : (A : Set) -> (A -> Set) -> Set
      piType <- do
        av <- mkVar "A" 0
        b <- pi av set
        pi set =<< pi b set
      cod1' <- lam cod1
      cod2' <- lam cod2
      checkEqualApplySpine ctx1 piType [dom1, cod1'] ctx2 piType [dom2, cod2']
    (Set, Equal type1' l1 r1, Set, Equal type2' l2 r2) -> do
      -- _==_ : (A : Set) -> A -> A -> Set
      equalType_ <- do
        xv <- mkVar "A" 0
        yv <- mkVar "A" 1
        pi set =<< pi xv =<< pi yv set
      checkEqualApplySpine ctx1 equalType_ [type1', l1, r1] ctx2 equalType_ [type2', l2, r2]
    (Equal _ _ _, Refl, Equal _ _ _, Refl) -> do
      return []
    ( App (Def _) tyConPars10, Con dataCon dataConArgs1,
      App (Def _) tyConPars20, Con dataCon' dataConArgs2
      ) | dataCon == dataCon' -> do
       let Just tyConPars1 = mapM isApply tyConPars10
       let Just tyConPars2 = mapM isApply tyConPars20
       DataCon _ _ dataConTypeTel dataConType <- getDefinition dataCon
       appliedDataConType1 <- Tel.substs dataConTypeTel dataConType tyConPars1
       appliedDataConType2 <- Tel.substs dataConTypeTel dataConType tyConPars2
       checkEqualApplySpine ctx1 appliedDataConType1 dataConArgs1 ctx2 appliedDataConType2 dataConArgs2
    (Set, Set, Set, Set) -> do
      return []
    (_, App h1 elims1, _, App h2 elims2) | h1 == h2 -> do
      equalSpine h1 ctx1 elims1 ctx2 elims2
    (_, _, _, _) -> do
     checkError $ TermsNotEqual type1 t1 type2 t2

-- Pretty printing Constraints

instance PrettyM Constraint where
  prettyM c0 = do
    case c0 of
      Unify ctx1 type1 t1 ctx2 type2 t2 -> do
        ctx1Doc <- prettyM ctx1
        type1Doc <- prettyArgM type1
        t1Doc <- prettyArgM t1
        ctx2Doc <- prettyM ctx2
        type2Doc <- prettyArgM type2
        t2Doc <- prettyArgM t2
        return $ group $
          group (ctx1Doc <+> "|-" // group (t1Doc <+> ":" <+> type1Doc)) //
          hang 2 "=" //
          group (ctx2Doc <+> "|-" // group (t2Doc <+> ":" <+> type2Doc))
      UnifySpine ctx1 type1 mbH1 elims1 ctx2 type2 mbH2 elims2 -> do
        ctx1Doc <- prettyM ctx1
        type1Doc <- prettyArgM type1
        t1Doc <- prettyMbApp mbH1 elims1
        ctx2Doc <- prettyM ctx2
        type2Doc <- prettyArgM type2
        t2Doc <- prettyMbApp mbH2 elims2
        return $ group $
          group (ctx1Doc <+> "|-" // group (t1Doc <+> ":" <+> type1Doc)) //
          hang 2 "=" //
          group (ctx2Doc <+> "|-" // group (t2Doc <+> ":" <+> type2Doc))
      CheckAndInstantiate type_ term mv -> do
        typeDoc <- prettyArgM type_
        termDoc <- prettyArgM term
        return $
          "CheckAndInstantiate" $$
          "type:" //> typeDoc $$
          "term:" //> termDoc $$
          "metavar:" //> PP.pretty mv
    where
      prettyMbApp mbH elims = do
        hdoc <- case mbH of
          Nothing -> return "[]"
          Just t  -> do tDoc <- prettyTermM t
                        return $ group "[" // tDoc // "]"
        elimsDoc <- mapM prettyM elims
        return $ PP.prettyApp 4 hdoc elimsDoc
