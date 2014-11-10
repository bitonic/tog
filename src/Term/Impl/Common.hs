{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Term.Impl.Common
  ( genericApplySubst
  , genericWhnf
  , genericTypeOfJ
  , genericNf
  , genericSynEq
  , genericMetaVars
  , genericPrettyPrecM
  , genericCanStrengthen

  , view
  , unview
  ) where

import           Control.Monad.Trans.Maybe        (MaybeT(MaybeT), runMaybeT)
import qualified Data.HashSet                     as HS
import           Data.Traversable                 (mapM, sequence)

import           Conf
import           Prelude.Extended                 hiding (foldr, mapM, sequence)
import           Syntax
import qualified Syntax.Abstract                  as SA
import qualified PrettyPrint                      as PP
import           Term
import           Term.Types                       (unview, view)
import qualified Term.Substitution                as Sub
import           Term.Substitution.Types          as Sub
import qualified Term.Signature                   as Sig

genericApplySubst
  :: (IsTerm t, MonadTerm t m) => t -> Substitution t -> m t
genericApplySubst t Sub.Id = do
  return t
genericApplySubst t rho = do
  tView <- whnfView t
  case tView of
    Lam body ->
      lam =<< applySubst body (Sub.lift 1 rho)
    Pi dom cod ->
      join $ pi <$> applySubst dom rho <*> applySubst cod (Sub.lift 1 rho)
    Equal type_ x y  ->
      join $ equal <$> applySubst type_ rho
                   <*> applySubst x rho
                   <*> applySubst y rho
    Refl ->
      return refl
    Con dataCon args ->
      join $ con dataCon <$> applySubst args rho
    Set ->
      return set
    App h els  -> do
      els' <- applySubst els rho
      case h of
        Var v   -> (`eliminate` els') =<< Sub.lookup v rho
        Def n   -> app (Def n) els'
        Meta mv -> app (Meta mv) els'
        J       -> app J els'

genericCanStrengthen
  :: forall t m. (IsTerm t, MonadTerm t m) => t -> m (Maybe Name)
genericCanStrengthen = runMaybeT . go 0
  where
    go :: Natural -> t -> MaybeT m Name
    go ix t = do
      tView <- lift $ whnfView t
      case tView of
        App (Var v) _ | varIndex v == ix -> do
          return $ varName v
        App _ es -> do
          msum $ map goElim es
        Pi dom cod -> do
          go ix dom <|> go (ix+1) cod
        Lam body -> do
          go (ix+1) body
        Equal type_ x y -> do
          go ix type_ <|> go ix x <|> go ix y
        Refl -> do
          mzero
        Set -> do
          mzero
        Con _ ts -> do
          msum $ map (go ix) ts
      where
        goElim (Proj _)   = mzero
        goElim (Apply t') = go ix t'

genericWhnf
  :: (IsTerm t, MonadTerm t m) => t -> m (Blocked t)
genericWhnf t = do
  tView <- view t
  sig <- askSignature
  case tView of
    App (Meta mv) es | Just t' <- Sig.getMetaVarBody sig mv -> do
      whnf =<< eliminate t' es
    -- Note that here we don't want to crash if the definition is not
    -- set, since I want to be able to test non-typechecked terms.
    App (Def defName) es | Just (Function _ cs) <- Sig.getDefinition sig defName -> do
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
      mbN <- canStrengthen cod
      case mbN of
        Just n -> do
          SA.Pi n <$> internalToTerm dom <*> internalToTerm cod
        Nothing -> do
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
      let h' = case h of
            Var v -> SA.Var (SA.name (PP.render v))
            Def f -> SA.Def f
            J -> SA.J SA.noSrcLoc
            Meta mv -> SA.Var (SA.Name (SA.srcLoc mv) (PP.render mv))
      args' <- forM args $ \arg -> case arg of
        Apply t -> SA.Apply <$> internalToTerm t
        Proj p  -> return $ SA.Proj $ pName p
      return $ SA.App h' args'


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
