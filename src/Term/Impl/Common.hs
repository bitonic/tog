{-# LANGUAGE OverloadedStrings #-}
module Term.Impl.Common where

import           Prelude                          hiding (pi, foldr)

import           Bound                            (Var(B, F))
import qualified Bound.Name                       as Bound
import           Bound.Var                        (unvar)
import           Control.Applicative              (pure, (<*>), (<|>))
import           Control.Monad                    (msum, join)
import           Control.Monad.Trans              (lift)
import           Control.Monad.Trans.Maybe        (MaybeT(MaybeT), runMaybeT)
import           Data.Functor                     ((<$>))
import qualified Data.HashSet                     as HS
import           Data.Traversable                 (traverse)

import           Syntax.Internal                  (Name, DefName)
import           Term
import qualified Term.Signature                   as Sig
import qualified Text.PrettyPrint.Extended        as PP

-- TODO remove duplication between this and the actual `eliminate'
-- | Tries to apply the eliminators to the term.  Trows an error
-- when the term and the eliminators don't match.
substEliminate
  :: (SubstVar v, IsTerm t) => t v -> [Elim t v] -> TermM (t v)
substEliminate t elims = do
  tView <- view t
  case (tView, elims) of
    (_, []) ->
        return t
    (Con _c args, Proj _ field : es) ->
        if unField field >= length args
        then error "substEliminate: Bad elimination"
        else substEliminate (args !! unField field) es
    (Lam body, Apply argument : es) -> do
        body' <- instantiate body argument
        substEliminate body' es
    (App h es1, es2) ->
        app h (es1 ++ es2)
    (_, _) ->
        error $ "substEliminate: Bad elimination"

genericSubstView
  :: (SubstVar a, SubstVar b, IsTerm t) => TermView t a -> (a -> TermM (t b)) -> TermM (t b)
genericSubstView tView f = do
  case tView of
    Lam body ->
      lam =<< genericSubst body (lift' f)
    Pi dom cod ->
      join $ pi <$> subst dom f <*> subst cod (lift' f)
    Equal type_ x y  ->
      join $ equal <$> subst type_ f <*> subst x f <*> subst y f
    Refl ->
      return refl
    Con dataCon args ->
      join $ con dataCon <$> mapM (`subst` f) args
    Set ->
      return set
    App h els  -> do
      els' <- mapM (mapElimM (`subst` f)) els
      case h of
        Var v   -> do t' <- f v; substEliminate t' els'
        Def n   -> app (Def n) els'
        Meta mv -> app (Meta mv) els'
        J       -> app J els'
  where
    lift' :: (IsTerm t, SubstVar a, SubstVar b)
          => (a -> TermM (t b))
          -> (TermVar a -> TermM (Abs t b))
    lift' _ (B v) = var $ B v
    lift' g (F v) = weaken =<< g v

genericSubst
  :: (SubstVar a, SubstVar b, IsTerm t) => t a -> (a -> TermM (t b)) -> TermM (t b)
genericSubst t f = do
  tView <- view t
  genericSubstView tView f

genericWhnf
  :: (SubstVar v, IsTerm t) => Sig.Signature t -> t v -> TermM (Blocked t v)
genericWhnf sig t = do
  tView <- view t
  case tView of
    App (Meta mv) es | Just t' <- Sig.getMetaVarBody sig mv -> do
      whnf sig =<< eliminate sig (substVacuous t') es
    App (Def defName) es | Function _ cs <- Sig.getDefinition sig defName -> do
      mbT <- whnfFun sig defName es $ ignoreInvertible cs
      case mbT of
        Just t' -> return t'
        Nothing -> return $ NotBlocked t
    App J (_ : x : _ : _ : Apply p : Apply refl' : es) -> do
      refl'' <- whnf sig refl'
      reflView <- view =<< ignoreBlocking refl''
      case reflView of
        Refl -> whnf sig =<< eliminate sig p (x : es)
        _    -> return $ NotBlocked t
    App (Meta mv) elims ->
      return $ MetaVarHead mv elims
    _ ->
      return $ NotBlocked t

whnfFun
  :: (SubstVar v, IsTerm t)
  => Sig.Signature t
  -> DefName -> [Elim t v] -> [Closed (Clause t)]
  -> TermM (Maybe (Blocked t v))
whnfFun _ _ _ [] = do
  return Nothing
whnfFun sig funName es (Clause patterns body : clauses) = runMaybeT $ do
  matched <- lift $ matchClause sig es patterns
  case matched of
    TTMetaVars mvs ->
      return $ BlockedOn mvs funName es
    TTFail () ->
      MaybeT $ whnfFun sig funName es clauses
    TTOK (args, leftoverEs) -> lift $ do
      body' <- instantiateClauseBody body args
      whnf sig =<< eliminate sig body' leftoverEs

matchClause
  :: (SubstVar v, IsTerm t)
  => Sig.Signature t
  -> [Elim t v] -> [Pattern]
  -> TermM (TermTraverse () ([t v], [Elim t v]))
matchClause _ es [] =
  return $ pure ([], es)
matchClause sig (Apply arg : es) (VarP : patterns) = do
  matched <- matchClause sig es patterns
  return $ (\(args, leftoverEs) -> (arg : args, leftoverEs)) <$> matched
matchClause sig (Apply arg : es) (ConP dataCon dataConPatterns : patterns) = do
  blockedArg <- whnf sig arg
  case blockedArg of
    MetaVarHead mv _ -> do
      matched <- matchClause sig es patterns
      return $ TTMetaVars (HS.singleton mv) <*> matched
    NotBlocked t -> do
      tView <- view t
      case tView of
        Con dataCon' dataConArgs | dataCon == dataCon' ->
          matchClause sig (map Apply dataConArgs ++ es) (dataConPatterns ++ patterns)
        _ ->
          return $ TTFail ()
    _ ->
      return $ TTFail ()
matchClause _ _ _ =
  return $ TTFail ()

genericGetAbsName
  :: forall t v0.
     (SubstVar v0, IsTerm t)
  => Abs t v0 -> TermM (Maybe Name)
genericGetAbsName = go $ \v -> case v of
  B v' -> Just $ Bound.name v'
  F _  -> Nothing
  where
    lift' _ (B _) = Nothing
    lift' f (F v) = f v

    go :: (SubstVar v) => (v -> Maybe Name) -> t v -> TermM (Maybe Name)
    go f t = do
      tView <- view t
      case tView of
        Lam body -> go (lift' f) body
        Pi dom cod -> (<|>) <$> go f dom <*> go (lift' f) cod
        Equal type_ x y -> msum <$> mapM (go f) [type_, x, y]
        Refl -> return Nothing
        Con _ args -> msum <$> mapM (go f) args
        Set -> return Nothing
        App h els -> do
          let mbN = case h of
                Var v -> f v
                _     -> Nothing
          ((mbN <|>) . msum) <$>
            mapM (foldElim (go f) (\_ _ -> return Nothing)) els

genericStrengthen
  :: (SubstVar v, IsTerm t) => Abs t v -> TermM (Maybe (t v))
genericStrengthen = runMaybeT . go (unvar (const Nothing) Just)
  where
    lift' :: (v -> Maybe v0) -> (TermVar v -> Maybe (TermVar v0))
    lift' _ (B _) = Nothing
    lift' f (F v) = F <$> f v

    go :: (SubstVar v, SubstVar v0, IsTerm t)
       => (v -> Maybe v0) -> t v -> MaybeT TermM (t v0)
    go f t = do
      tView <- lift $ view t
      case tView of
        Lam body -> do
          lift . lam =<< go (lift' f) body
        Pi dom cod -> do
          dom' <- go f dom
          cod' <- go (lift' f) cod
          lift $ pi dom' cod'
        Equal type_ x y  -> do
          type' <- go f type_
          x' <- go f x
          y' <- go f y
          lift $ equal type' x' y'
        Refl -> do
          return refl
        Con dataCon args -> do
          lift . con dataCon =<< mapM (go f) args
        Set -> do
          return set
        App h els -> do
          h' <- MaybeT $ return $ traverse f h
          els' <- mapM (mapElimM (go f)) els
          lift $ app h' els'

genericNf :: forall t v. (SubstVar v, IsTerm t) => Sig.Signature t -> t v -> TermM (t v)
genericNf sig t = do
  tView <- whnfView sig t
  case tView of
    Lam body ->
      lam =<< nf sig body
    Pi domain codomain ->
      join $ pi <$> nf sig domain <*> nf sig codomain
    Equal type_ x y ->
      join $ equal <$> nf sig type_ <*> nf sig x <*> nf sig y
    Refl ->
      return refl
    Con dataCon args ->
      join $ con dataCon <$> mapM (nf sig) args
    Set ->
      return set
    App h elims ->
      join $ app h <$> mapM (nf' sig) elims

-- (A : Set) ->
-- (x : A) ->
-- (y : A) ->
-- (P : (x : A) -> (y : A) -> (eq : _==_ A x y) -> Set) ->
-- (p : (x : A) -> P x x refl) ->
-- (eq : _==_ A x y) ->
-- P x y eq
genericTypeOfJ :: forall t. (IsTerm t) => TermM (Closed (Type t))
genericTypeOfJ =
  substMap close =<<
    ("A", return set) -->
    ("x", var "A") -->
    ("y", var "A") -->
    ("P", ("x", var "A") --> ("y", var "A") -->
          ("eq", join (equal <$> var "A" <*> var "x" <*> var "y")) -->
          return set
    ) -->
    ("p", ("x", var "A") --> (app (Var "P") . map Apply =<< sequence [var "x", var "x", return refl])) -->
    ("eq", join (equal <$> var "A" <*> var "x" <*> var "y")) -->
    (app (Var "P") . map Apply =<< sequence [var "x", var "y", return refl])
  where
    close v = error $ "genericTypeOfJ: Free variable " ++ PP.render v

    infixr 9 -->
    (-->) :: (Name, TermM (t Name)) -> TermM (t Name) -> TermM (t Name)
    (x, type_) --> t = do
      type' <- type_
      t' <- t
      pi type' =<< abstract x t'

genericTermEq
  :: (IsTerm t, SubstVar v)
  => t v -> t v -> TermM Bool
genericTermEq t1 t2 = do
  join $ genericTermViewEq <$> view t1 <*> view t2

genericTermViewEq
  :: (IsTerm t, SubstVar v)
  => TermView t v -> TermView t v -> TermM Bool
genericTermViewEq tView1 tView2 = do
  case (tView1, tView2) of
    (Lam body1, Lam body2) ->
      termEq body1 body2
    (Pi domain1 codomain1, Pi domain2 codomain2) ->
      (&&) <$> termEq domain1 domain2 <*> termEq codomain1 codomain2
    (Equal type1 x1 y1, Equal type2 x2 y2) ->
      (&&) <$> ((&&) <$> termEq type1 type2 <*> termEq x1 x2)
           <*> termEq y1 y2
    (App h1 els1, App h2 els2) ->
      (h1 == h2 &&) <$> elimsEq els1 els2
    (Set, Set) ->
      return True
    (Con dataCon1 args1, Con dataCon2 args2) | dataCon1 == dataCon2 ->
      argsEq args1 args2
    (Refl, Refl) ->
      return True
    (_, _) -> do
      return False
  where
    elimsEq []           []           = return True
    elimsEq (el1 : els1) (el2 : els2) = (&&) <$> elimEq el1 el2 <*> elimsEq els1 els2
    elimsEq _            _            = return False

    elimEq (Apply t1')  (Apply t2')  = termEq t1' t2'
    elimEq (Proj n1 f1) (Proj n2 f2) = return $ n1 == n2 && f1 == f2
    elimEq _            _            = return False

    argsEq []             []             = return True
    argsEq (arg1 : args1) (arg2 : args2) = (&&) <$> termEq arg1 arg2 <*> argsEq args1 args2
    argsEq _              _              = return False
