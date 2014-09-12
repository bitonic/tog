{-# LANGUAGE OverloadedStrings #-}
module Term.Impl.Common
  ( genericSubsts
  , genericWhnf
  , genericGetAbsName
  , genericStrengthen
  , genericWeaken
  , genericTypeOfJ
  , genericNf
  , genericTermEq
  , matchClause
  ) where

import           Prelude                          hiding (pi, foldr)

import           Control.Monad.Trans.Maybe        (MaybeT(MaybeT), runMaybeT)
import qualified Data.HashSet                     as HS

import           Prelude.Extended
import           Syntax.Internal                  (Name)
import           Term
import qualified Term.Signature                   as Sig

-- TODO remove duplication between this and the actual `eliminate'
-- | Tries to apply the eliminators to the term.  Trows an error
-- when the term and the eliminators don't match.
substEliminate
  :: (IsTerm t) => t -> [Elim t] -> TermM t
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

genericSubstsView
  :: forall t. (IsTerm t) => [(Int, t)] -> TermView t -> TermM t
genericSubstsView [] tView = do
  unview tView
genericSubstsView args tView = do
  case tView of
    Lam body ->
      lam =<< subst' body
    Pi dom cod ->
      join $ pi <$> substs args dom <*> subst' cod
    Equal type_ x y  ->
      join $ equal <$> substs args type_ <*> substs args x <*> substs args y
    Refl ->
      return refl
    Con dataCon args' ->
      join $ con dataCon <$> mapM (substs args) args'
    Set ->
      return set
    App h els  -> do
      els' <- mapM (mapElimM (substs args)) els
      case h of
        Var v   -> case lookup (varIndex v) args of
                     Nothing  -> app (Var v) els'
                     Just arg -> substEliminate arg els'
        Def n   -> app (Def n) els'
        Meta mv -> app (Meta mv) els'
        J       -> app J els'
  where
    subst' t' = do
      args' <- forM args $ \(ix, arg) -> do
        arg' <- weaken_ 1 arg
        return (ix + 1, arg')
      substs args' t'

genericSubsts
  :: (IsTerm t) => [(Int, t)] -> t -> TermM t
genericSubsts [] t = do
  return t
genericSubsts args t = do
  tView <- view t
  genericSubstsView args tView

genericWhnf
  :: (IsTerm t) => Sig.Signature t -> t -> TermM (Blocked t)
genericWhnf sig t = do
  tView <- view t
  case tView of
    App (Meta mv) es | Just t' <- Sig.getMetaVarBody sig mv -> do
      whnf sig =<< eliminate sig t' es
    App (Def defName) es | Function _ cs <- Sig.getDefinition sig defName -> do
      mbT <- whnfFun sig defName es $ ignoreInvertible cs
      case mbT of
        Just t' -> return t'
        Nothing -> return $ NotBlocked t
    App J es0@(_ : x : _ : _ : Apply p : Apply refl' : es) -> do
      refl'' <- whnf sig refl'
      case refl'' of
        MetaVarHead mv _ ->
          return $ BlockedOn (HS.singleton mv) BlockedOnJ es0
        BlockedOn mvs _ _ ->
          return $ BlockedOn mvs BlockedOnJ es0
        NotBlocked refl''' -> do
          reflView <- view refl'''
          case reflView of
            Refl -> whnf sig =<< eliminate sig p (x : es)
            _    -> return $ NotBlocked t
    App (Meta mv) elims ->
      return $ MetaVarHead mv elims
    _ ->
      return $ NotBlocked t

whnfFun
  :: (IsTerm t)
  => Sig.Signature t
  -> Name -> [Elim t] -> [Closed (Clause t)]
  -> TermM (Maybe (Blocked t))
whnfFun _ _ _ [] = do
  return Nothing
whnfFun sig funName es (Clause patterns body : clauses) = runMaybeT $ do
  matched <- lift $ matchClause sig es patterns
  case matched of
    TTMetaVars mvs ->
      return $ BlockedOn mvs (BlockedOnFunction funName) es
    TTFail () ->
      MaybeT $ whnfFun sig funName es clauses
    TTOK (args, leftoverEs) -> lift $ do
      body' <- instantiateClauseBody body args
      whnf sig =<< eliminate sig body' leftoverEs

matchClause
  :: (IsTerm t)
  => Sig.Signature t
  -> [Elim t] -> [Pattern]
  -> TermM (TermTraverse () ([t], [Elim t]))
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
    BlockedOn mvs _ _ -> do
      matched <- matchClause sig es patterns
      return $ TTMetaVars mvs <*> matched
    NotBlocked t -> do
      tView <- view t
      case tView of
        Con dataCon' dataConArgs | dataCon == dataCon' ->
          matchClause sig (map Apply dataConArgs ++ es) (dataConPatterns ++ patterns)
        _ ->
          return $ TTFail ()
matchClause _ _ _ =
  return $ TTFail ()

genericGetAbsName
  :: forall t.
     (IsTerm t)
  => Abs t -> TermM (Maybe Name)
genericGetAbsName =
  go $ \v -> if varIndex v == 0 then Just (varName v) else Nothing
  where
    lift' :: (Var -> Maybe Name) -> Var -> Maybe Name
    lift' f v = f =<< strengthenVar_ 1 v

    go :: (Var -> Maybe Name) -> t -> TermM (Maybe Name)
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
  :: (IsTerm t) => Int -> Int -> Abs t -> TermM (Maybe t)
genericStrengthen from0 by = runMaybeT . go from0
  where
    go :: (IsTerm t)
       => Int -> t -> MaybeT TermM t
    go from t = do
      tView <- lift $ view t
      case tView of
        Lam body -> do
          lift . lam =<< go (from + 1) body
        Pi dom cod -> do
          dom' <- go from dom
          cod' <- go (from + 1) cod
          lift $ pi dom' cod'
        Equal type_ x y  -> do
          type' <- go from type_
          x' <- go from x
          y' <- go from y
          lift $ equal type' x' y'
        Refl -> do
          return refl
        Con dataCon args -> do
          lift . con dataCon =<< mapM (go from) args
        Set -> do
          return set
        App h els -> do
          h' <- MaybeT $ return $ case h of
            Var v -> Var <$> strengthenVar from by v
            _     -> Just h
          els' <- mapM (mapElimM (go from)) els
          lift $ app h' els'

genericNf :: forall t . (IsTerm t) => Sig.Signature t -> t -> TermM t
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
    ("A", r set) -->
    ("x", v "A" 0) -->
    ("y", v "A" 1) -->
    ("P", ("x", v "A" 2) --> ("y", v "A" 3) -->
          ("eq", join (equal <$> v "A" 4 <*> v "x" 1 <*> v "y" 0)) -->
          r set
    ) -->
    ("p", ("x", v "A" 3) --> (app (Var (V (Named "P" 1))) . map Apply =<< sequence [v "x" 0, v "x" 0, r refl])) -->
    ("eq", join (equal <$> v "A" 4 <*> v "x" 3 <*> v "y" 2)) -->
    (app (Var (V (Named "P" 2))) . map Apply =<< sequence [v "x" 4, v "y" 3, v "eq" 0])
  where
    v n ix = var $ V $ Named n ix
    r = return

    infixr 9 -->
    (-->) :: (Name, TermM t) -> TermM t -> TermM t
    (_, type_) --> t = join $ pi <$> type_ <*> t

genericTermEq
  :: (IsTerm t)
  => t -> t -> TermM Bool
genericTermEq t1 t2 = do
  join $ genericTermViewEq <$> view t1 <*> view t2

genericTermViewEq
  :: (IsTerm t)
  => TermView t -> TermView t -> TermM Bool
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
    argsEq []             []             = return True
    argsEq (arg1 : args1) (arg2 : args2) = (&&) <$> termEq arg1 arg2 <*> argsEq args1 args2
    argsEq _              _              = return False

genericWeaken
  :: (IsTerm t)
  => Int -> Int -> t -> TermM t
genericWeaken from by t = do
  tView <- view t
  case tView of
    Lam body ->
      lam =<< weaken (from + 1) by body
    Pi dom cod ->
      join $ pi <$> weaken from by dom <*> weaken (from + 1) by cod
    Equal type_ x y  ->
      join $ equal <$> weaken from by type_
                   <*> weaken from by x
                   <*> weaken from by y
    Refl ->
      return refl
    Con dataCon args ->
      join $ con dataCon <$> mapM (weaken from by) args
    Set ->
      return set
    App h els  -> do
      els' <- mapM (mapElimM (weaken from by)) els
      case h of
        Var v   -> let v' = if varIndex v >= from
                            then weakenVar from by v
                            else v
                   in app (Var v') els'
        Def n   -> app (Def n) els'
        Meta mv -> app (Meta mv) els'
        J       -> app J els'
