{-# LANGUAGE OverloadedStrings #-}
module Term.Impl.Common
  ( genericApplySubst
  , genericWhnf
  , genericGetAbsName
  , genericStrengthen
  , genericWeaken
  , genericTypeOfJ
  , genericNf
  , genericSynEq
  , genericMetaVars
  , genericPrettyPrecM
  ) where

import           Prelude                          hiding (pi, foldr, mapM, sequence)

import           Control.Lens                     (firstOf)
import           Control.Monad.Trans.Maybe        (MaybeT(MaybeT), runMaybeT)
import qualified Data.HashSet                     as HS
import           Data.Traversable                 (mapM, sequence)

import           Conf
import           Prelude.Extended
import           Syntax
import qualified Syntax.Internal                  as SI
import qualified PrettyPrint                      as PP
import           Term
import qualified Term.Substitution                as Sub
import           Term.Substitution.Types          as Sub
import qualified Term.Signature                   as Sig

genericApplySubstView
  :: forall t m. (IsTerm t, MonadTerm t m) => Substitution t -> TermView t -> m t
genericApplySubstView Sub.Id tView = do
  unview tView
genericApplySubstView rho tView = do
  case tView of
    Lam body ->
      lam =<< applySubst rho body
    Pi dom cod ->
      join $ pi <$> applySubst rho dom <*> applySubst rho cod
    Equal type_ x y  ->
      join $ equal <$> applySubst rho type_
                   <*> applySubst rho x
                   <*> applySubst rho y
    Refl ->
      return refl
    Con dataCon args ->
      join $ con dataCon <$> applySubst rho args
    Set ->
      return set
    App h els  -> do
      els' <- applySubst rho els
      case h of
        Var v   -> (`eliminate` els') =<< Sub.lookup v rho
        Def n   -> app (Def n) els'
        Meta mv -> app (Meta mv) els'
        J       -> app J els'

genericApplySubst
  :: (IsTerm t, MonadTerm t m) => Substitution t -> t -> m t
genericApplySubst args t = do
  tView <- view t
  genericApplySubstView args tView

genericWhnf
  :: (IsTerm t, MonadTerm t m) => t -> m (Blocked t)
genericWhnf t = do
  tView <- view t
  sig <- askSignature
  case tView of
    App (Meta mv) es | Just t' <- Sig.getMetaVarBody sig mv -> do
      whnf =<< eliminate t' es
    App (Def defName) es | Function _ cs <- Sig.getDefinition sig defName -> do
      mbT <- whnfFun defName es $ ignoreInvertible cs
      case mbT of
        Just t' -> return t'
        Nothing -> return $ NotBlocked t
    App J es0@(_ : x : _ : _ : Apply p : Apply refl' : es) -> do
      refl'' <- whnf refl'
      case refl'' of
        MetaVarHead mv _ ->
          return $ BlockedOn (HS.singleton mv) BlockedOnJ es0
        BlockedOn mvs _ _ ->
          return $ BlockedOn mvs BlockedOnJ es0
        NotBlocked refl''' -> do
          reflView <- view refl'''
          case reflView of
            Refl -> whnf =<< eliminate p (x : es)
            _    -> return $ NotBlocked t
    App (Meta mv) elims ->
      return $ MetaVarHead mv elims
    _ ->
      return $ NotBlocked t

whnfFun
  :: (IsTerm t, MonadTerm t m)
  => Name -> [Elim t] -> [Closed (Clause t)]
  -> m (Maybe (Blocked t))
whnfFun _ _ [] = do
  return Nothing
whnfFun funName es (Clause patterns body : clauses) = runMaybeT $ do
  matched <- lift $ matchClause es patterns
  case matched of
    TTMetaVars mvs ->
      return $ BlockedOn mvs (BlockedOnFunction funName) es
    TTFail () ->
      MaybeT $ whnfFun funName es clauses
    TTOK (args, leftoverEs) -> lift $ do
      body' <- instantiateClauseBody body args
      whnf =<< eliminate body' leftoverEs

matchClause
  :: (IsTerm t, MonadTerm t m)
  => [Elim t] -> [Pattern]
  -> m (TermTraverse () ([t], [Elim t]))
matchClause es [] =
  return $ pure ([], es)
matchClause (Apply arg : es) (VarP : patterns) = do
  matched <- matchClause es patterns
  return $ (\(args, leftoverEs) -> (arg : args, leftoverEs)) <$> matched
matchClause (Apply arg : es) (ConP dataCon dataConPatterns : patterns) = do
  blockedArg <- whnf arg
  case blockedArg of
    MetaVarHead mv _ -> do
      matched <- matchClause es patterns
      return $ TTMetaVars (HS.singleton mv) <*> matched
    BlockedOn mvs _ _ -> do
      matched <- matchClause es patterns
      return $ TTMetaVars mvs <*> matched
    NotBlocked t -> do
      tView <- view t
      case tView of
        Con dataCon' dataConArgs | dataCon == dataCon' ->
          matchClause (map Apply dataConArgs ++ es) (dataConPatterns ++ patterns)
        _ ->
          return $ TTFail ()
matchClause _ _ =
  return $ TTFail ()

genericGetAbsName
  :: forall t m.
     (IsTerm t, MonadTerm t m)
  => Abs t -> m (Maybe Name)
genericGetAbsName =
  go $ \v -> if varIndex v == 0 then Just (varName v) else Nothing
  where
    lift' :: (Var -> Maybe Name) -> Var -> Maybe Name
    lift' f v = f =<< strengthenVar_ 1 v

    go :: (Var -> Maybe Name) -> t -> m (Maybe Name)
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
          els' <- forM els $ fmap (join . firstOf traverse) . traverse (go f)
          return $ mbN <|> msum els'

genericStrengthen
  :: (IsTerm t, MonadTerm t m) => Int -> Int -> Abs t -> m (Maybe t)
genericStrengthen from0 by = runMaybeT . go from0
  where
    go :: (IsTerm t, MonadTerm t m)
       => Int -> t -> MaybeT m t
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
          els' <- mapM (mapM (go from)) els
          lift $ app h' els'

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
    ("p", ("x", v "A" 3) --> (app (Var (V (Named "P" 1))) . map Apply =<< sequence [v "x" 0, v "x" 0, r refl])) -->
    ("eq", join (equal <$> v "A" 4 <*> v "x" 3 <*> v "y" 2)) -->
    (app (Var (V (Named "P" 2))) . map Apply =<< sequence [v "x" 4, v "y" 3, v "eq" 0])
  where
    v n ix = var $ V $ Named n ix
    r = return

    infixr 9 -->
    (-->) :: (Name, m t) -> m t -> m t
    (_, type_) --> t = join $ pi <$> type_ <*> t

genericSynEq
  :: (IsTerm t, MonadTerm t m)
  => t -> t -> m Bool
genericSynEq t1 t2 = do
  join $ genericTermViewEq <$> view t1 <*> view t2

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
      (h1 == h2 &&) <$> synEq els1 els2
    (Set, Set) ->
      return True
    (Con dataCon1 args1, Con dataCon2 args2) | dataCon1 == dataCon2 ->
      synEq args1 args2
    (Refl, Refl) ->
      return True
    (_, _) -> do
      return False

genericWeaken
  :: (IsTerm t, MonadTerm t m)
  => Int -> Int -> t -> m t
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
      els' <- mapM (mapM (weaken from by)) els
      case h of
        Var v   -> let v' = if varIndex v >= from
                            then weakenVar from by v
                            else v
                   in app (Var v') els'
        Def n   -> app (Def n) els'
        Meta mv -> app (Meta mv) els'
        J       -> app J els'

instantiateClauseBody
  :: (IsTerm t, MonadTerm t m) => ClauseBody t -> [Term t] -> m (Term t)
instantiateClauseBody body args = error "TODO instantiateClauseBody" -- instantiate body args

genericPrettyPrecM
  :: (IsTerm t, MonadTerm t m) => Int -> t -> m PP.Doc
genericPrettyPrecM p t = do
    synT <- internalToTerm t
    return $ PP.prettyPrec p synT

internalToTerm
  :: (IsTerm t, MonadTerm t m) => t -> m SI.Expr
internalToTerm t0 = do
  dontNormalize <- confDontNormalizePP <$> readConf
  tView <- view =<< if dontNormalize then return t0 else nf t0
  case tView of
    Lam body -> do
      n <- getAbsName_ body
      SI.Lam n <$> internalToTerm body
    Pi dom cod -> do
      mbN <- canStrengthen cod
      case mbN of
        Just n -> do
          SI.Pi n <$> internalToTerm dom <*> internalToTerm cod
        Nothing -> do
          SI.Fun <$> internalToTerm dom <*> internalToTerm cod
    Equal type_ x y ->
      SI.Equal <$> internalToTerm type_ <*> internalToTerm x <*> internalToTerm y
    Refl ->
      return $ SI.Refl SI.noSrcLoc
    Con dataCon args ->
      SI.Con dataCon <$> mapM internalToTerm args
    Set ->
      return $ SI.Set SI.noSrcLoc
    App h args -> do
      let h' = case h of
            Var v -> SI.Var (SI.name (PP.render v))
            Def f -> SI.Def f
            J -> SI.J SI.noSrcLoc
            Meta mv -> SI.Var (SI.Name (SI.srcLoc mv) (PP.render mv))
      args' <- forM args $ \arg -> case arg of
        Apply t -> SI.Apply <$> internalToTerm t
        Proj p  -> return $ SI.Proj $ pName p
      return $ SI.App h' args'


genericMetaVars :: (IsTerm t, MonadTerm t m) => Term t -> m MetaVarSet
genericMetaVars t = do
  tView <- whnfView t
  case tView of
    Lam body           -> metaVars body
    Pi domain codomain -> (<>) <$> metaVars domain <*> metaVars codomain
    Equal type_ x y    -> mconcat <$> mapM metaVars [type_, x, y]
    App h elims        -> (<>) <$> metaVarsHead h <*> metaVars elims
    Set                -> return mempty
    Refl               -> return mempty
    Con _ elims        -> metaVars elims
  where
    metaVarsHead (Meta mv) = return $ HS.singleton mv
    metaVarsHead _         = return mempty
