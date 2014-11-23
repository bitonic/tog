{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Term.Impl.Common
  ( genericSafeApplySubst
  , genericWhnf
  , genericTypeOfJ
  , genericNf
  , genericSynEq
  , genericMetas
  , genericPrettyPrecM

  , view
  , unview
  ) where

import qualified Data.HashSet                     as HS
import           Data.Traversable                 (mapM, sequence)

import           Instrumentation
import           Prelude.Extended                 hiding (foldr, mapM, sequence)
import           Syntax
import qualified Syntax.Abstract                  as SA
import qualified PrettyPrint                      as PP
import           Term.Synonyms
import           Term.Types
import qualified Term.Subst                       as Sub
import           Data.Collect

#include "impossible.h"

genericSafeApplySubst
  :: (IsTerm t, MonadTerm t m) => t -> Subst t -> ApplySubstM m t
genericSafeApplySubst t Sub.Id = do
  return t
genericSafeApplySubst t rho = do
  -- TODO note that here
  -- * With `view', GR is as fast as S with `whnfView', but S is impossibly slow;
  -- * With `whnfView', GR is almost twice as slow as S.
  reduce <- confWhnfApplySubst <$> readConf
  tView <- lift $ if reduce then whnfView t else view t
  case tView of
    Lam body ->
      lift . lam =<< safeApplySubst body (subLift 1 rho)
    Pi dom cod -> do
      dom' <- safeApplySubst dom rho
      cod' <- safeApplySubst cod $ subLift 1 rho
      lift $ pi dom' cod'
    Equal type_ x y  -> do
      type' <- safeApplySubst type_ rho
      x' <- safeApplySubst x rho
      y' <- safeApplySubst y rho
      lift $ equal type' x' y'
    Refl ->
      return refl
    Con dataCon args -> do
      args' <- safeApplySubst args rho
      lift $ con dataCon args'
    Set ->
      return set
    App h els  -> do
      els' <- safeApplySubst els rho
      case h of
        Var v   -> do u <- subLookup v rho
                      lift $ eliminate u els'
        Def n   -> lift $ app (Def n) els'
        J       -> lift $ app J els'

genericWhnf
  :: (IsTerm t, MonadTerm t m) => t -> m (Blocked Meta t)
genericWhnf t = do
  tView <- view t
  let fallback = return $ NotBlocked t
  case tView of
    App (Def opnd@(Opened dkey _)) es -> do
      sig <- askSignature
      -- Note that here we don't want to crash if the definition is not
      -- set, since I want to be able to test non-typechecked terms.
      case sigLookupDefinition sig dkey of
        Just (Contextual tel (Constant _ (Instantiable inst))) -> do
          eliminateInst tel opnd inst es
        _ -> do
          fallback
    App J es0@(_ : x : _ : _ : Apply p : Apply refl' : es) -> do
      refl'' <- whnf refl'
      case refl'' of
        BlockingHead bl _ ->
          -- return $ BlockedOn (HS.singleton bl) BlockedOnJ es0
          return $ BlockedOn (HS.singleton (opndKey bl)) BlockedOnJ es0
        BlockedOn mvs _ _ ->
          return $ BlockedOn mvs BlockedOnJ es0
        NotBlocked refl''' -> do
          reflView <- view refl'''
          case reflView of
            Refl -> whnf =<< eliminate p (x : es)
            _    -> fallback
    _ ->
      fallback

eliminateInst
  :: (IsTerm t, MonadTerm t m)
  => Tel t -> Opened DefKey t -> Inst t -> [Elim t]
  -> m (Blocked Meta t)
eliminateInst _ (Opened (DKMeta mv) args) Open es = do
  return $ BlockingHead (Opened mv args) es
eliminateInst _ (Opened (DKName f) args) Open es = do
  NotBlocked <$> defName (Opened f args) es
eliminateInst tel opnd@(Opened _ args) (Inst inv) es | clauses <- ignoreInvertible inv = do
  -- Optimization: if the arguments are all lined up, don't touch
  -- the body.
  --
  -- This is a special case, we know that all meta-variable bodies and
  -- where clauses will be stored in this form, and we want to
  -- optimize for that.  If some functions fall under this pattern
  -- too, it doesn't matter.

  -- The number of arguments must be the same as the length of the
  -- context telescope.
  _assert@True <- return $ length args == telLength tel
  simple <- isSimple (length args - 1) args
  clauses' <- if simple
    then return clauses
    else instantiate clauses args
  eliminateClauses opnd clauses' es
  where
    isSimple _ [] = do
      return True
    isSimple n' (arg : args') = do
      argView <- view arg
      case argView of
        App (Var v) [] | varIndex v == n' -> isSimple (n'-1) args'
        _                                 -> return False

eliminateClauses
  :: (IsTerm t, MonadTerm t m)
  => Opened DefKey t -> [Clause t] -> [Elim t] -> m (Blocked Meta t)
-- Again, metas only ever have one clause.  Note that all these are just
-- assertions, things would work just fine without them, but let's
-- program defensively.
eliminateClauses (Opened (DKMeta _) _) [Clause [] t] es = do
  whnf =<< eliminate t es
eliminateClauses (Opened (DKMeta _) _) _ _  = do
  __IMPOSSIBLE__
eliminateClauses (Opened (DKName f) args) clauses es = do
  let opnd = Opened f args
  mbT <- whnfFun opnd es clauses
  case mbT of
    Nothing -> NotBlocked <$> defName opnd es
    Just t  -> return t

whnfFun
  :: (IsTerm t, MonadTerm t m)
  => Opened Name t -> [Elim t] -> [Clause t]
  -> m (Maybe (Blocked Meta t))
whnfFun _ _ [] = do
  return Nothing
whnfFun fun es (Clause patterns body : clauses) = runMaybeT $ do
  matched <- lift $ matchClause es patterns
  case matched of
    Failure (CCollect mvs) ->
      return $ BlockedOn mvs (BlockedOnFunction fun) es
    Failure (CFail ()) ->
      MaybeT $ whnfFun fun es clauses
    Success (args, leftoverEs) -> lift $ do
      body' <- instantiateClauseBody body args
      whnf =<< eliminate body' leftoverEs

matchClause
  :: (IsTerm t, MonadTerm t m)
  => [Elim t] -> [Pattern]
  -> m (Validation (Collect_ MetaSet) ([t], [Elim t]))
matchClause es [] =
  return $ pure ([], es)
matchClause (Apply arg : es) (VarP : patterns) = do
  matched <- matchClause es patterns
  return $ (\(args, leftoverEs) -> (arg : args, leftoverEs)) <$> matched
matchClause (Apply arg : es) (ConP dataCon dataConPatterns : patterns) = do
  blockedArg <- whnf arg
  case blockedArg of
    BlockingHead bl _ -> do
      matched <- matchClause es patterns
      return $ Failure (CCollect (HS.singleton (opndKey bl))) <*> matched
    BlockedOn mvs _ _ -> do
      matched <- matchClause es patterns
      return $ Failure (CCollect mvs) <*> matched
    NotBlocked t -> do
      tView <- view t
      case tView of
        Con dataCon' dataConArgs | dataCon == dataCon' ->
          matchClause (map Apply dataConArgs ++ es) (dataConPatterns ++ patterns)
        _ ->
          return $ Failure $ CFail ()
matchClause _ _ =
  return $ Failure $ CFail ()

genericNf :: forall t m. (IsTerm t, MonadTerm t m) => t -> m t
genericNf t = do
  tView <- whnfView t
  case tView of
    Lam body ->
      lam =<< nf body
    Pi domain codomain ->
      join $ pi <$> nf domain <*> nf codomain
    Equal type_ x y ->
      join $ equal <$> nf type_ <*> nf x <*> nf y
    Refl ->
      return refl
    Con dataCon args ->
      join $ con dataCon <$> mapM nf args
    Set ->
      return set
    App h elims ->
      join $ app h <$> mapM nf elims

-- (A : Set) ->
-- (x : A) ->
-- (y : A) ->
-- (P : (x : A) -> (y : A) -> (eq : _==_ A x y) -> Set) ->
-- (p : (x : A) -> P x x refl) ->
-- (eq : _==_ A x y) ->
-- P x y eq
genericTypeOfJ :: forall t m. (IsTerm t, MonadTerm t m) => m (Closed (Type t))
genericTypeOfJ =
    ("A", r set) -->
    ("x", v "A" 0) -->
    ("y", v "A" 1) -->
    ("P", ("x", v "A" 2) --> ("y", v "A" 3) -->
          ("eq", join (equal <$> v "A" 4 <*> v "x" 1 <*> v "y" 0)) -->
          r set
    ) -->
    ("p", ("x", v "A" 3) --> (app (Var (mkVar "P" 1)) . map Apply =<< sequence [v "x" 0, v "x" 0, r refl])) -->
    ("eq", join (equal <$> v "A" 4 <*> v "x" 3 <*> v "y" 2)) -->
    (app (Var (mkVar "P" 2)) . map Apply =<< sequence [v "x" 4, v "y" 3, v "eq" 0])
  where
    v n ix = var $ mkVar n ix
    r = return

    infixr 9 -->
    (-->) :: (Name, m t) -> m t -> m t
    (_, type_) --> t = join $ pi <$> type_ <*> t

genericSynEq
  :: (IsTerm t, MonadTerm t m)
  => t -> t -> m Bool
genericSynEq t1 t2 = do
  join $ genericTermViewEq <$> whnfView t1 <*> whnfView t2

genericTermViewEq
  :: (IsTerm t, MonadTerm t m)
  => TermView t -> TermView t -> m Bool
genericTermViewEq tView1 tView2 = do
  case (tView1, tView2) of
    (Lam body1, Lam body2) ->
      synEq body1 body2
    (Pi domain1 codomain1, Pi domain2 codomain2) ->
      (&&) <$> synEq domain1 domain2 <*> synEq codomain1 codomain2
    (Equal type1 x1 y1, Equal type2 x2 y2) ->
      (&&) <$> ((&&) <$> synEq type1 type2 <*> synEq x1 x2)
           <*> synEq y1 y2
    (App h1 els1, App h2 els2) ->
      synEq (h1, els1) (h2, els2)
    (Set, Set) ->
      return True
    (Con dataCon1 args1, Con dataCon2 args2) | dataCon1 == dataCon2 ->
      synEq args1 args2
    (Refl, Refl) ->
      return True
    (_, _) -> do
      return False

instantiateClauseBody
  :: (IsTerm t, MonadTerm t m) => ClauseBody t -> [Term t] -> m (Term t)
instantiateClauseBody = instantiate

genericPrettyPrecM
  :: (IsTerm t, MonadTerm t m) => Int -> t -> m PP.Doc
genericPrettyPrecM p t = do
    synT <- internalToTerm t
    return $ PP.prettyPrec p synT

internalToTerm
  :: (IsTerm t, MonadTerm t m) => t -> m SA.Expr
internalToTerm t0 = do
  dontNormalize <- confDontNormalizePP <$> readConf
  tView <- view =<< if dontNormalize then return t0 else nf t0
  case tView of
    Lam body -> do
      n <- getAbsName_ body
      SA.Lam n <$> internalToTerm body
    Pi dom cod -> do
      mbN <- runApplySubst $ safeApplySubst cod $ subStrengthen 1 subId
      case mbN of
        Left n -> do
          SA.Pi n <$> internalToTerm dom <*> internalToTerm cod
        Right _ -> do
          SA.Fun <$> internalToTerm dom <*> internalToTerm cod
    Equal type_ x y ->
      SA.Equal <$> internalToTerm type_ <*> internalToTerm x <*> internalToTerm y
    Refl ->
      return $ SA.Refl SA.noSrcLoc
    Con dataCon args ->
      SA.Con dataCon <$> mapM internalToTerm args
    Set ->
      return $ SA.Set SA.noSrcLoc
    App h args -> do
      (h', args1) <- case h of
        Var v ->
          return (SA.Var (SA.name (PP.render v)), [])
        Def (Opened (DKName f) args') ->
          (SA.Def f,) <$> mapM internalToTerm args'
        Def (Opened (DKMeta mv) args') ->
          (SA.Var (SA.Name (SA.srcLoc mv) (PP.render mv)),) <$> mapM internalToTerm args'
        J ->
          return (SA.J SA.noSrcLoc, [])
      args2 <- forM args $ \arg -> case arg of
        Apply t -> SA.Apply <$> internalToTerm t
        Proj p  -> return $ SA.Proj $ pName p
      return $ SA.App h' (map SA.Apply args1 ++ args2)

genericMetas :: (IsTerm t, MonadTerm t m) => Term t -> m MetaSet
genericMetas t = do
  tView <- whnfView t
  case tView of
    Lam body           -> metas body
    Pi domain codomain -> (<>) <$> metas domain <*> metas codomain
    Equal type_ x y    -> mconcat <$> mapM metas [type_, x, y]
    App h elims        -> (<>) <$> metasHead h <*> metas elims
    Set                -> return mempty
    Refl               -> return mempty
    Con _ elims        -> metas elims
  where
    metasHead (Def (Opened k args)) = do
      mvs <- metas args
      let mv = case k of
            DKName _   -> mempty
            DKMeta mv' -> HS.singleton mv'
      return $ mv <> mvs
    metasHead _ = do
      return mempty
