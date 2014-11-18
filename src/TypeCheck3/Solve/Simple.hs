{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
module TypeCheck3.Solve.Simple
  ( SolveState
  , initSolveState
  , solve
  ) where

import           Control.Monad.State.Strict       (get, put)
import           Control.Monad.Trans.Writer.Strict (execWriterT, tell)
import qualified Data.HashSet                     as HS
import qualified Data.Set                         as Set
import           Syntax

import           Conf
import           Prelude.Extended
import           PrettyPrint                      (($$), (<+>), (//>), (//), group, indent, hang)
import qualified PrettyPrint                      as PP
import           Term

import qualified Term.Telescope                   as Tel
import qualified Term.Subst                as Sub
import qualified TypeCheck3.Common                as Common
import           TypeCheck3.Common                hiding (Constraint(..), Constraints)
import           TypeCheck3.Monad
import           TypeCheck3.Check
import           TypeCheck3.Solve.Common

-- These definitions should be in every Solve module
----------------------------------------------------

newtype SolveState t = SolveState (Constraints t)

type BlockingMetas = HS.HashSet MetaVar
type Constraints t = [(BlockingMetas, Constraint t)]

data Constraint t
  = Unify (Ctx t) (Type t) (Term t) (Term t)
  | UnifySpine (Ctx t) (Type t) (Maybe (Term t)) [Elim (Term t)] [Elim (Term t)]
  | Conj [Constraint t]
  | (:>>:) (Constraint t) (Constraint t)

simplify :: Constraint t -> Maybe (Constraint t)
simplify (Conj [])    = Nothing
simplify (Conj [c])   = simplify c
simplify (Conj cs)    = msum $ map simplify $ concatMap flatten cs
  where
    flatten (Conj constrs) = concatMap flatten constrs
    flatten c              = [c]
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

constraint :: (IsTerm t) => Common.Constraint t -> Constraint t
constraint (Common.JmEq ctx type1 t1 type2 t2) =
  Unify ctx set type1 type2 :>>: Unify ctx type1 t1 t2

initSolveState :: SolveState t
initSolveState = SolveState []

solve :: forall t. (IsTerm t) => Common.Constraint t -> TC t (SolveState t) ()
solve c = do
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
          "constraint:" //> constrDoc
  debugSection "solveConstraint" msg $ do
    case constr0 of
      Conj constrs -> do
        mconcat <$> forM constrs solveConstraint
      Unify ctx type_ t1 t2 -> do
        checkEqual (ctx, type_, t1, t2)
      UnifySpine ctx type_ mbH elims1 elims2 -> do
        checkEqualSpine' ctx type_ mbH elims1 elims2
      constr1 :>>: constr2 -> do
        constrs1_0 <- solveConstraint constr1
        let mbConstrs1 = mconcat [ fmap (\c -> [(mvs, c)]) (simplify constr)
                                 | (mvs, constr) <- constrs1_0 ]
        case mbConstrs1 of
          Nothing -> do
            solveConstraint constr2
          Just constrs1 -> do
            let (mvs, constr1') = mconcat constrs1
            return [(mvs, constr1' :>>: constr2)]

instance PrettyM t (SolveState t) where
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

sequenceConstraints :: Constraints t -> Constraint t -> Constraints t
sequenceConstraints scs1 c2 =
  let (css, cs1) = unzip scs1 in [(mconcat css, Conj cs1 :>>: c2)]

-- Equality
------------------------------------------------------------------------

type CheckEqual t = (Ctx t, Type t, Term t, Term t)

data CheckEqualProgress t
  = Done (Constraints t)
  | KeepGoing (CheckEqual t)

done :: Constraints t -> TC t s (CheckEqualProgress t)
done = return . Done

keepGoing :: CheckEqual t -> TC t s (CheckEqualProgress t)
keepGoing = return . KeepGoing

checkEqual
  :: (IsTerm t) => CheckEqual t -> TC t s (Constraints t)
checkEqual (ctx0, type0, t1_0, t2_0) = do
  let msg = do
        ctxDoc <- prettyM ctx0
        typeDoc <- prettyM type0
        xDoc <- prettyM t1_0
        yDoc <- prettyM t2_0
        return $
          "ctx:" //> ctxDoc $$
          "type:" //> typeDoc $$
          "x:" //> xDoc $$
          "y:" //> yDoc
  debugSection "unify" msg $ do
    runCheckEqual
      [ checkSynEq              -- Optimization: check if the two terms are equal
      , etaExpand'              -- Expand the terms
      , checkMetaVars           -- Assign/intersect metavariables if needed
      ]
      compareTerms
      (ctx0, type0, t1_0, t2_0)
  where
    runCheckEqual actions0 finally args = do
      case actions0 of
        []                 -> finally args
        (action : actions) -> do
          constrsOrArgs <- action args
          case constrsOrArgs of
            Done constrs    -> return constrs
            KeepGoing args' -> runCheckEqual actions finally args'

checkSynEq
  :: (IsTerm t)
  => CheckEqual t -> TC t s (CheckEqualProgress t)
checkSynEq args@(ctx, type_, t1, t2) = do
  disabled <- confDisableSynEquality <$> readConf
  if disabled
    then do
      keepGoing args
    else do
      debugBracket_ "checkSynEq" "" $ do
        -- Optimization: try with a simple syntactic check first.
        t1' <- ignoreBlocking =<< whnf t1
        t2' <- ignoreBlocking =<< whnf t2
        -- TODO add option to skip this check
        eq <- synEq t1' t2'
        if eq
          then done []
          else keepGoing (ctx, type_, t1', t2')

etaExpand'
  :: (IsTerm t)
  => CheckEqual t -> TC t s (CheckEqualProgress t)
etaExpand' (ctx, type0, t1, t2) = do
  debugBracket_ "etaExpand" "" $ do
    t1' <- etaExpand type0 t1
    t2' <- etaExpand type0 t2
    keepGoing (ctx, type0, t1', t2')

checkMetaVars
  :: (IsTerm t)
  => CheckEqual t -> TC t s (CheckEqualProgress t)
checkMetaVars (ctx, type_, t1, t2) = do
  blockedT1 <- whnf t1
  t1' <- ignoreBlocking blockedT1
  blockedT2 <- whnf t2
  t2' <- ignoreBlocking blockedT2
  let syntacticEqualityOrPostpone mvs = do
        t1'' <- nf t1'
        t2'' <- nf t2'
        eq <- synEq t1'' t2''
        if eq
          then done []
          else do
            debug_ "both sides blocked" $ "waiting for" <+> PP.pretty (HS.toList mvs)
            done [(mvs, Unify ctx type_ t1'' t2'')]
  case (blockedT1, blockedT2) of
    (MetaVarHead mv els1, MetaVarHead mv' els2) | mv == mv' -> do
      mbKills <- intersectVars els1 els2
      case mbKills of
        Nothing -> do
          syntacticEqualityOrPostpone $ HS.singleton mv
        Just kills -> do
          mvType <- getMetaVarType mv
          newMv <- addMetaVar mvType
          instantiateMetaVar mv =<< killArgs newMv kills
          done []
    (MetaVarHead mv elims, _) -> do
      done =<< metaAssign ctx type_ mv elims t2
    (_, MetaVarHead mv elims) -> do
      done =<< metaAssign ctx type_ mv elims t1
    (BlockedOn mvs1 _ _, BlockedOn mvs2 _ _) -> do
      -- Both blocked, and we already checked for syntactic equality,
      -- let's try syntactic equality when normalized.
      syntacticEqualityOrPostpone (mvs1 <> mvs2)
    (BlockedOn mvs f elims, _) -> do
      done =<< checkEqualBlockedOn ctx type_ mvs f elims t2
    (_, BlockedOn mvs f elims) -> do
      done =<< checkEqualBlockedOn ctx type_ mvs f elims t1
    (NotBlocked _, NotBlocked _) -> do
      keepGoing (ctx, type_, t1', t2')

checkEqualBlockedOn
  :: forall t s.
     (IsTerm t)
  => Ctx t -> Type t
  -> HS.HashSet MetaVar -> BlockedHead -> [Elim t]
  -> Term t
  -> TC t s (Constraints t)
checkEqualBlockedOn ctx type_ mvs bh elims1 t2 = do
  let msg = "Equality blocked on metavars" <+> PP.pretty (HS.toList mvs) <>
            ", trying to invert definition" <+> PP.pretty bh
  t1 <- ignoreBlocking $ BlockedOn mvs bh elims1
  debugBracket_ "checkEqualBlockedOn" msg $ do
    case bh of
      BlockedOnJ -> do
        debug_ "head is J, couldn't invert." ""
        fallback t1
      BlockedOnFunction fun1 -> do
        Function _ clauses <- getDefinition fun1
        case clauses of
          NotInvertible _ -> do
            debug_ "couldn't invert." ""
            fallback t1
          Invertible injClauses -> do
            t2View <- whnfView t2
            case t2View of
              App (Def fun2) elims2 | fun1 == fun2 -> do
                debug_ "could invert, and same heads, checking spines." ""
                equalSpine (Def fun1) ctx elims1 elims2
              _ -> do
                t2Head <- termHead t2
                case t2Head of
                  Nothing -> do
                    debug_ "definition invertible but we don't have a clause head." ""
                    fallback t1
                  Just tHead | Just (Clause pats _) <- lookup tHead injClauses -> do
                    debug_ ("inverting on" <+> PP.pretty tHead) ""
                    -- Make the eliminators match the patterns
                    matched <- matchPats pats elims1
                    -- And restart, if we matched something.
                    if matched
                      then do
                        debug_ "matched constructor, restarting" ""
                        checkEqual (ctx, type_, t1, t2)
                      else do
                        debug_ "couldn't match constructor" ""
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
  h' <- app h []
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
        typeDoc <- prettyM type_
        hDoc <- case mbH of
          Nothing -> return "No head"
          Just h  -> prettyM h
        elims1Doc <- prettyM $ elim1 : elims1
        elims2Doc <- prettyM $ elim2 : elims2
        return $
          "type:" //> typeDoc $$
          "head:" //> hDoc $$
          "elims1:" //> elims1Doc $$
          "elims2:" //> elims2Doc
  debugBracket "checkEqualSpine" msg $ do
    case (elim1, elim2) of
      (Apply arg1, Apply arg2) -> do
        Pi dom cod <- whnfView type_
        res1 <- checkEqual (ctx, dom, arg1, arg2)
        mbCod <- strengthenTerm cod
        mbH' <- traverse (`eliminate` [Apply arg1]) mbH
        -- If the rest is non-dependent, we can continue immediately.
        case mbCod of
          Just cod' -> do
            res2 <- checkEqualSpine' ctx cod' mbH' elims1 elims2
            return (res1 <> res2)
          Nothing -> do
            cod' <- instantiate_ cod arg1
            return $ sequenceConstraints res1 (UnifySpine ctx cod' mbH' elims1 elims2)
      (Proj proj, Proj proj') | proj == proj' -> do
          let Just h = mbH
          (h', type') <- applyProjection proj h type_
          checkEqualSpine' ctx type' (Just h') elims1 elims2
      _ ->
        checkError $ SpineNotEqual type_ (elim1 : elims1) type_ (elim1 : elims2)
checkEqualSpine' _ type_ _ elims1 elims2 = do
  checkError $ SpineNotEqual type_ elims1 type_ elims2

metaAssign
  :: (IsTerm t)
  => Ctx t -> Type t -> MetaVar -> [Elim (Term t)] -> Term t
  -> TC t s (Constraints t)
metaAssign ctx0 type0 mv elims t0 = do
  mvType <- getMetaVarType mv
  let msg = do
        mvTypeDoc <- prettyM mvType
        elimsDoc <- prettyM elims
        tDoc <- prettyM t0
        return $
          "assigning metavar:" <+> PP.pretty mv $$
          "of type:" //> mvTypeDoc $$
          "elims:" //> elimsDoc $$
          "to term:" //> tDoc
  let fallback mvs = do
        mvT <- metaVar mv elims
        return [(mvs, Unify ctx0 type0 mvT t0)]
  debugBracket "metaAssign" msg $ do
    -- See if we can invert the metavariable
    invOrMvs <- do
      tt <- invertMetaVar ctx0 elims
      return $ case tt of
        TTOK x         -> Right x
        TTFail ()      -> Left $ HS.singleton mv
        TTMetaVars mvs -> Left $ HS.insert mv mvs
    case invOrMvs of
      Left mvs -> do
        debug_ "couldn't invert" ""
        -- If we can't invert, try to prune the variables not
        -- present on the right from the eliminators.
        t' <- nf t0
        -- TODO should we really prune allowing all variables here?  Or
        -- only the rigid ones?
        fvs <- fvAll <$> freeVars t'
        elims' <- nf elims
        mbMvT <- prune fvs mv elims'
        -- If we managed to prune them, restart the equality.
        -- Otherwise, wait on the metavariables.
        case mbMvT of
          Nothing -> do
            fallback mvs
          Just mvT -> do
            mvT' <- eliminate mvT elims'
            checkEqual (ctx0, type0, mvT', t')
      Right (ctx, acts, inv) -> do
        t <- applySubst t0 acts
        type_ <- applySubst type0 acts
        whenDebug $ unless (Sub.null acts) $ debug "could invert, new stuff" $ do
          tDoc <- prettyM t
          typeDoc <- prettyM type_
          ctxDoc <- prettyM ctx
          return $
            "ctx:" //> ctxDoc $$
            "type:" //> typeDoc $$
            "term:" //> tDoc
        debug "could invert" $ do
          invDoc <- prettyM inv
          return $ "inversion:" //> invDoc
        t1 <- pruneTerm (Set.fromList $ invertMetaVarVars inv) t
        debug "pruned term" $ prettyM t1
        t2 <- applyInvertMetaVar ctx inv t1
        case t2 of
          TTOK mvb -> do
            mvs <- metaVars $ mvbBody mvb
            when (mv `HS.member` mvs) $
              checkError $ OccursCheckFailed mv $ mvbBody mvb
            instantiateMetaVar mv mvb
            return []
          TTMetaVars mvs -> do
            debug_ ("inversion blocked on" //> PP.pretty (HS.toList mvs)) ""
            fallback mvs
          TTFail v ->
            checkError $ FreeVariableInEquatedTerm mv elims t v

compareTerms :: (IsTerm t) => CheckEqual t -> TC t s (Constraints t)
compareTerms (ctx, type_, t1, t2) = do
  typeView <- whnfView type_
  t1View <- whnfView t1
  t2View <- whnfView t2
  case (typeView, t1View, t2View) of
    -- Note that here we rely on canonical terms to have canonical
    -- types, and on the terms to be eta-expanded.
    (Pi dom cod, Lam body1, Lam body2) -> do
      -- TODO there is a bit of duplication between here and expansion.
      name <- getAbsName_ body1
      ctx' <- extendContext ctx (name, dom)
      checkEqual (ctx', cod, body1, body2)
    (Set, Pi dom1 cod1, Pi dom2 cod2) -> do
      -- Pi : (A : Set) -> (A -> Set) -> Set
      piType <- do
        av <- var $ mkVar "A" 0
        b <- pi av set
        pi set =<< pi b set
      cod1' <- lam cod1
      cod2' <- lam cod2
      checkEqualApplySpine ctx piType [dom1, cod1'] [dom2, cod2']
    (Set, Equal type1' l1 r1, Equal type2' l2 r2) -> do
      -- _==_ : (A : Set) -> A -> A -> Set
      equalType_ <- do
        xv <- var $ mkVar "A" 0
        yv <- var $ mkVar "A" 1
        pi set =<< pi xv =<< pi yv set
      checkEqualApplySpine ctx equalType_ [type1', l1, r1] [type2', l2, r2]
    (Equal _ _ _, Refl, Refl) -> do
      return []
    (App (Def _) tyConPars0, Con dataCon dataConArgs1, Con dataCon' dataConArgs2) | dataCon == dataCon' -> do
       let Just tyConPars = mapM isApply tyConPars0
       DataCon _ _ dataConTypeTel dataConType <- getDefinition dataCon
       appliedDataConType <- Tel.discharge dataConTypeTel dataConType tyConPars
       checkEqualApplySpine ctx appliedDataConType dataConArgs1 dataConArgs2
    (Set, Set, Set) -> do
      return []
    (_, App h elims1, App h' elims2) | h == h' -> do
      equalSpine h ctx elims1 elims2
    (_, _, _) -> do
     checkError $ TermsNotEqual type_ t1 type_ t2


-- Pretty printing Constraints

instance PrettyM t (Constraint t) where
  prettyM c0 = do
    case fromMaybe c0 (simplify c0) of
      Unify ctx type_ t1 t2 -> do
        ctxDoc <- prettyM ctx
        typeDoc <- prettyM type_
        t1Doc <- prettyM t1
        t2Doc <- prettyM t2
        return $ group $
          ctxDoc <+> "|-" //
          group (t1Doc // hang 2 "=" // t2Doc // hang 2 ":" // typeDoc)
      c1 :>>: c2 -> do
        c1Doc <- prettyM c1
        c2Doc <- prettyM c2
        return $ group (indent 2 (group c1Doc) $$ ">>" $$ indent 2 (group c2Doc))
      Conj cs -> do
        csDoc <- mapM prettyM cs
        return $
          "Conj" //> PP.list csDoc
      UnifySpine ctx type_ mbH elims1 elims2 -> do
        ctxDoc <- prettyM ctx
        typeDoc <- prettyM type_
        hDoc <- case mbH of
          Nothing -> return "no head"
          Just h  -> prettyM h
        elims1Doc <- prettyM elims1
        elims2Doc <- prettyM elims2
        return $
          "UnifySpine" $$
          "ctx:" //> ctxDoc $$
          "type:" //> typeDoc $$
          "h:" //> hDoc $$
          "elims1:" //> elims1Doc $$
          "elims2:" //> elims2Doc
