{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Tog.Unify.Simple
  ( SolveState
  , initSolveState
  , solve
  ) where

import           Control.Monad.Trans.Writer.Strict (execWriterT, tell)
import qualified Data.HashSet                     as HS
import qualified Data.Set                         as Set

import           Tog.Instrumentation
import           Tog.Names
import           Tog.Prelude
import           Tog.PrettyPrint                  (($$), (<+>), (//>), (//), group, indent, hang)
import qualified Tog.PrettyPrint                  as PP
import           Tog.Term
import qualified Tog.Elaborate                    as Elaborate
import           Tog.Monad
import           Tog.TypeCheck
import           Tog.Unify.Common
import           Tog.Error

#include "impossible.h"

-- These definitions should be in every Solve module
----------------------------------------------------

type ConstraintId = Natural

type Constraints t = [([ConstraintId], MetaSet, Constraint t)]
type Constraints_ t = [(MetaSet, Constraint t)]

data Constraint t
  = Unify SrcLoc (Ctx t) (Type t) (Term t) (Term t)
  | UnifySpine SrcLoc (Ctx t) (Type t) (Maybe (Term t)) [Elim (Term t)] [Elim (Term t)]
  | Conj [Constraint t]
  | (:>>:) (Constraint t) (Constraint t)

data SolveState t = SolveState
  { _ssConstraintCount :: !ConstraintId
  , _ssConstraints     :: !(Constraints t)
  }

makeLenses ''SolveState

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

constraint :: (IsTerm t) => Elaborate.Constraint t -> Constraint t
constraint (Elaborate.JmEq loc ctx type1 t1 type2 t2) =
  Unify loc ctx set type1 type2 :>>: Unify loc ctx type1 t1 t2

initSolveState :: SolveState t
initSolveState = SolveState 0 []

solve :: forall t r. (IsTerm t) => Elaborate.Constraint t -> TC t r (SolveState t) ()
solve c = do
  debugBracket_ "solve" "" $ do
    count <- bumpCount
    let constr = ([count], mempty, constraint c)
    ssConstraints %= (constr :)
    go False []
  where
    bumpCount = do
      ssConstraintCount %= (+1)
      use ssConstraintCount

    popConstr = do
      constrs <- use ssConstraints
      case constrs of
        [] -> do
          return Nothing
        (c' : cs) -> do
          ssConstraints .= cs
          return $ Just c'

    newConstraint (constrId, mvs, constr) =
      debug "newConstraint" $ do
        constrDoc <- prettyM constr
        return $
          "constrId:" //> PP.pretty constrId $$
          "mvs:" //> PP.pretty (HS.toList mvs) $$
          "constr:" //> constrDoc

    go :: Bool -> Constraints t -> TC t r (SolveState t) ()
    go progress newConstrs = do
      mbConstr <- popConstr
      case mbConstr of
        Nothing -> do
          ssConstraints .= newConstrs
          if progress
            then go False []
            else return ()
        Just (constrIds, mvs, constr) -> do
          attempt <- do mvsBodies <- mapM lookupMetaBody (HS.toList mvs)
                        return $ null mvsBodies || any isJust mvsBodies
          if attempt
            then do
              untaggedConstrs <- solveConstraint constrIds constr
              constrs <- forM untaggedConstrs $ \(mvs', constr') -> do
                constrId' <- bumpCount
                let taggedConstr = (constrId' : constrIds, mvs', constr')
                newConstraint taggedConstr
                return taggedConstr
              go True (constrs ++ newConstrs)
            else do
              go progress ((constrIds, mvs, constr) : newConstrs)

solveConstraint :: (IsTerm t) => [ConstraintId] -> Constraint t -> TC t r s (Constraints_ t)
solveConstraint constrId constr0 = do
  let msg = do
        constrDoc <- prettyM constr0
        return $
          "constrId:" //> PP.pretty constrId $$
          "constr:" //> constrDoc
  debug "solveConstraint" msg
  execConstraint constr0

execConstraint :: (IsTerm t) => Constraint t -> TC t r s (Constraints_ t)
execConstraint constr0 = case constr0 of
  Conj constrs -> do
    mconcat <$> forM constrs execConstraint
  Unify loc ctx type_ t1 t2 -> atSrcLoc loc $ do
    checkEqual (ctx, type_, t1, t2)
  UnifySpine loc ctx type_ mbH elims1 elims2 -> atSrcLoc loc $ do
    checkEqualSpine' ctx type_ mbH elims1 elims2
  constr1 :>>: constr2 -> do
    constrs1_0 <- execConstraint constr1
    let mbConstrs1 = mconcat [ fmap (\c -> [(mvs, c)]) (simplify constr)
                             | (mvs, constr) <- constrs1_0 ]
    case mbConstrs1 of
      Nothing -> do
        execConstraint constr2
      Just constrs1 -> do
        let (mvs, constr1') = mconcat constrs1
        return [(mvs, constr1' :>>: constr2)]

instance PrettyM t (SolveState t) where
  prettyM (SolveState _ cs0) = do
     detailed <- confProblemsReport <$> readConf
     let go cs = do
           tell $ "-- Unsolved problems:" <+> PP.pretty (length cs)
           when detailed $ forM_ cs $ \(cId, mvs, c) -> do
             tell $ PP.line <> "------------------------------------------------------------------------"
             cDoc <- lift $ prettyM c
             tell $ PP.line <> "** Waiting on" <+> PP.pretty cId <+>
                    "[" <> PP.pretty (HS.toList mvs) <> "]" $$ cDoc
     execWriterT $ go cs0

-- This is local stuff
----------------------

sequenceConstraints :: (IsTerm t) => Constraints_ t -> Constraint t -> TC_ t (Constraints_ t)
sequenceConstraints [] c2 = execConstraint c2
sequenceConstraints scs1 c2 =
  let (css, cs1) = unzip scs1 in return [(mconcat css, Conj cs1 :>>: c2)]

-- Equality
------------------------------------------------------------------------

type CheckEqual t = (Ctx t, Type t, Term t, Term t)

data CheckEqualProgress t
  = Done (Constraints_ t)
  | KeepGoing (CheckEqual t)

done :: Constraints_ t -> TC t r s (CheckEqualProgress t)
done = return . Done

keepGoing :: CheckEqual t -> TC t r s (CheckEqualProgress t)
keepGoing = return . KeepGoing

checkEqual
  :: (IsTerm t) => CheckEqual t -> TC t r s (Constraints_ t)
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
  debugBracket "unify" msg $ do
    runCheckEqual
      [ checkSynEq              -- Optimization: check if the two terms are equal
      , etaExpand'              -- Expand the terms
      , checkMetas           -- Assign/intersect metavariables if needed
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
  => CheckEqual t -> TC t r s (CheckEqualProgress t)
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
  => CheckEqual t -> TC t r s (CheckEqualProgress t)
etaExpand' (ctx, type0, t1, t2) = do
  t1' <- etaExpand type0 t1
  t2' <- etaExpand type0 t2
  keepGoing (ctx, type0, t1', t2')

checkMetas
  :: (IsTerm t)
  => CheckEqual t -> TC t r s (CheckEqualProgress t)
checkMetas (ctx, type_, t1, t2) = do
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
            loc <- askSrcLoc
            done [(mvs, Unify loc ctx type_ t1'' t2'')]
  case (blockedT1, blockedT2) of
    (BlockingHead mv els1, BlockingHead mv' els2) | mv == mv' -> do
      mbKills <- intersectVars els1 els2
      case mbKills of
        Nothing -> do
          syntacticEqualityOrPostpone $ HS.singleton mv
        Just kills -> do
          mvType <- getMetaType mv
          newMv <- addMeta mvType
          instantiateMeta mv =<< killArgs newMv kills
          done []
    (BlockingHead mv elims, _) -> do
      done =<< metaAssign ctx type_ mv elims t2
    (_, BlockingHead mv elims) -> do
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
  :: forall t r s.
     (IsTerm t)
  => Ctx t -> Type t
  -> HS.HashSet Meta -> BlockedHead t -> [Elim t]
  -> Term t
  -> TC t r s (Constraints_ t)
checkEqualBlockedOn ctx type_ mvs bh elims1 t2 = do
  let msg = do
        bhDoc <- prettyM bh
        return $ "Equality blocked on metavars" <+> PP.pretty (HS.toList mvs) <>
                  ", trying to invert definition" <+> bhDoc
  t1 <- ignoreBlocking $ BlockedOn mvs bh elims1
  debugBracket "checkEqualBlockedOn" msg $ do
    case bh of
      BlockedOnJ -> do
        debug_ "head is J, couldn't invert." ""
        fallback t1
      BlockedOnFunction fun1 -> do
        Constant _ (Function (Inst clauses)) <- getDefinition fun1
        case clauses of
          NotInvertible _ -> do
            debug_ "couldn't invert." ""
            fallback t1
          Invertible injClauses -> do
            t2View <- whnfView t2
            let notInvertible = do
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
            case t2View of
              App (Def fun2) elims2 -> do
                sameFun <- synEq fun1 fun2
                if sameFun
                  then do
                    debug_ "could invert, and same heads, checking spines." ""
                    equalSpine (Def fun1) ctx elims1 elims2
                  else notInvertible
              _ -> do
                notInvertible
  where
    fallback t1 = do
      loc <- askSrcLoc
      return $ [(mvs, Unify loc ctx type_ t1 t2)]

    matchPats :: [Pattern t] -> [Elim t] -> TC t r s Bool
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

    matchPat :: Opened QName t -> [Pattern t] -> Elim t -> TC t r s Bool
    matchPat (Opened _ (_:_)) _ _ = do
      return False              -- TODO make this work in all cases.
    matchPat openedDataCon@(Opened dataCon []) pats (Apply t) = do
      tView <- whnfView t
      case tView of
        App (Meta mv) mvArgs -> do
          mvT <- instantiateDataCon mv dataCon
          void $ matchPat openedDataCon pats . Apply =<< eliminate mvT mvArgs
          return True
        Con dataCon' dataConArgs | dataCon == opndKey dataCon' -> do
          matchPats pats (map Apply dataConArgs)
        _ -> do
          -- This can happen -- when we are blocked on metavariables
          -- that are impeding other definitions.
          return False
    matchPat _ _ _ = do
      -- Same as above.
      return False

-- | @instantiateDataCon α c@ makes it so that @α := c β₁ ⋯ βₙ@, where
--   @c@ is a data constructor.
--
--   Pre: @α : Δ → D t₁ ⋯ tₙ@, where @D@ is the fully applied type
--   constructor for @c@.
--
--   TODO right now this works only with a simple 'Name', but we should
--   make it work for 'Opened Name' too.
instantiateDataCon
  :: (IsTerm t)
  => Meta
  -> QName
  -- ^ Name of the datacon
  -> TC t r s (Closed (Term t))
instantiateDataCon mv dataCon = do
  let openedDataCon = Opened dataCon []
  mvType <- getMetaType mv
  (telMvArgs, endType') <- unrollPi mvType
  DataCon tyCon _ dataConType <- getDefinition openedDataCon
  -- We know that the metavariable must have the right type (we have
  -- typechecked the arguments already).
  App (Def tyCon') tyConArgs0 <- whnfView endType'
  Just tyConArgs <- return $ mapM isApply tyConArgs0
  True <- synEq tyCon tyCon'
  appliedDataConType <- openContextual dataConType tyConArgs
  (dataConArgsTel, _) <- unrollPi appliedDataConType
  dataConArgs <- createMvsPars (telToCtx telMvArgs) dataConArgsTel
  mvT <- con openedDataCon dataConArgs
  let mi = MetaBody (telLength telMvArgs) mvT
  -- given the usage, here we know that the body is going to be well typed.
  -- TODO make sure that the above holds.
  instantiateMeta mv mi
  metaBodyToTerm mi

equalSpine
  :: (IsTerm t)
  => Head t -> Ctx t -> [Elim t] -> [Elim t] -> TC t r s (Constraints_ t)
equalSpine h ctx elims1 elims2 = do
  hType <- headType ctx h
  checkEqualSpine ctx hType h elims1 elims2

checkEqualApplySpine
  :: (IsTerm t)
  => Ctx t -> Type t -> [Term t] -> [Term t]
  -> TC t r s (Constraints_ t)
checkEqualApplySpine ctx type_ args1 args2 =
  checkEqualSpine' ctx type_ Nothing (map Apply args1) (map Apply args2)

checkEqualSpine
  :: (IsTerm t)
  => Ctx t -> Type t -> Head t -> [Elim (Term t)] -> [Elim (Term t)]
  -> TC t r s (Constraints_ t)
checkEqualSpine ctx type_ h elims1 elims2  = do
  h' <- app h []
  checkEqualSpine' ctx type_ (Just h') elims1 elims2

checkEqualSpine'
  :: (IsTerm t)
  => Ctx t -> Type t -> Maybe (Term t)
  -> [Elim (Term t)] -> [Elim (Term t)]
  -> TC t r s (Constraints_ t)
checkEqualSpine' ctx type_ mbH elims1 elims2 = do
  let msg = do
        typeDoc <- prettyM type_
        hDoc <- case mbH of
          Nothing -> return "No head"
          Just h  -> prettyM h
        elims1Doc <- prettyM elims1
        elims2Doc <- prettyM elims2
        return $
          "type:" //> typeDoc $$
          "head:" //> hDoc $$
          "elims1:" //> elims1Doc $$
          "elims2:" //> elims2Doc
  debugBracket "checkEqualSpine" msg $
    checkEqualSpine'' ctx type_ mbH elims1 elims2


checkEqualSpine''
  :: (IsTerm t)
  => Ctx t -> Type t -> Maybe (Term t)
  -> [Elim (Term t)] -> [Elim (Term t)]
  -> TC t r s (Constraints_ t)
checkEqualSpine'' _ _ _ [] [] = do
  return []
checkEqualSpine'' ctx type_ mbH (elim1 : elims1) (elim2 : elims2) = do
    let fallback =
          checkError $ SpineNotEqual type_ (elim1 : elims1) type_ (elim1 : elims2)
    case (elim1, elim2) of
      (Apply arg1, Apply arg2) -> do
        Pi dom cod <- whnfView type_
        res1 <- checkEqual (ctx, dom, arg1, arg2)
        mbCod <- safeStrengthen cod
        mbH' <- traverse (`eliminate` [Apply arg1]) mbH
        -- If the rest is non-dependent, we can continue immediately.
        case mbCod of
          Just cod' -> do
            res2 <- checkEqualSpine'' ctx cod' mbH' elims1 elims2
            return (res1 <> res2)
          Nothing -> do
            cod' <- instantiate_ cod arg1
            loc <- askSrcLoc
            sequenceConstraints res1 (UnifySpine loc ctx cod' mbH' elims1 elims2)
      (Proj proj, Proj proj') -> do
          sameProj <- synEq proj proj'
          if sameProj
            then do
              let Just h = mbH
              (h', type') <- applyProjection proj h type_
              checkEqualSpine'' ctx type' (Just h') elims1 elims2
            else do
              fallback
      _ ->
        fallback
checkEqualSpine'' _ type_ _ elims1 elims2 = do
  checkError $ SpineNotEqual type_ elims1 type_ elims2

metaAssign
  :: (IsTerm t)
  => Ctx t -> Type t -> Meta -> [Elim (Term t)] -> Term t
  -> TC t r s (Constraints_ t)
metaAssign ctx0 type0 mv elims t0 = do
  mvType <- getMetaType mv
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
        mvT <- meta mv elims
        loc <- askSrcLoc
        return [(mvs, Unify loc ctx0 type0 mvT t0)]
  debugBracket "metaAssign" msg $ do
    -- See if we can invert the metavariable
    invOrMvs <- do
      tt <- invertMeta ctx0 elims
      return $ case tt of
        Right x             -> Right x
        Left (CFail ())     -> Left $ HS.singleton mv
        Left (CCollect mvs) -> Left $ HS.insert mv mvs
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
        whenDebug $ unless (subNull acts) $ debug "could invert, new stuff" $ do
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
        t1 <- pruneTerm (Set.fromList $ invertMetaVars inv) t
        debug "pruned term" $ prettyM t1
        t2 <- applyInvertMeta ctx inv t1
        case t2 of
          Success mvb -> do
            mvs <- metas mvb
            when (mv `HS.member` mvs) $
              checkError $ OccursCheckFailed mv $ mbBody mvb
            instantiateMeta mv mvb
            return []
          Failure (CCollect mvs) -> do
            debug_ ("inversion blocked on" //> PP.pretty (HS.toList mvs)) ""
            fallback mvs
          Failure (CFail v) ->
            checkError $ FreeVariableInEquatedTerm mv elims t v

compareTerms :: (IsTerm t) => CheckEqual t -> TC t r s (Constraints_ t)
compareTerms (ctx, type_, t1, t2) = do
  typeView <- whnfView type_
  t1View <- whnfView t1
  t2View <- whnfView t2
  let fallback =
        checkError $ TermsNotEqual type_ t1 type_ t2
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
    (App (Def _) tyConPars0, Con dataCon dataConArgs1, Con dataCon' dataConArgs2) -> do
       sameDataCon <- synEq dataCon dataCon'
       if sameDataCon
         then do
           let Just tyConPars = mapM isApply tyConPars0
           DataCon _ _ dataConType <- getDefinition dataCon
           appliedDataConType <- openContextual dataConType tyConPars
           checkEqualApplySpine ctx appliedDataConType dataConArgs1 dataConArgs2
         else do
           fallback
    (Set, Set, Set) -> do
      return []
    (_, App h elims1, App h' elims2) -> do
      sameH <- synEq h h'
      if sameH then equalSpine h ctx elims1 elims2 else fallback
    (_, _, _) -> do
      fallback


-- Pretty printing Constraints

instance PrettyM t (Constraint t) where
  prettyM c0 = do
    case fromMaybe c0 (simplify c0) of
      Unify _ ctx type_ t1 t2 -> do
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
      UnifySpine _ ctx type_ mbH elims1 elims2 -> do
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
