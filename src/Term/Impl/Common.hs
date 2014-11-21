{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Term.Impl.Common
  ( genericSafeApplySubst
  , genericWhnf
  , genericTypeOfJ
  , genericNf
  , genericSynEq
  , genericMetaVars
  , genericPrettyPrecM

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
import qualified Term.Subst                as Sub
import           Term.Subst.Types          as Sub
import           Term.Subst.Utils          as Sub hiding (strengthen)
import qualified Term.Signature                   as Sig

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
      lift . lam =<< safeApplySubst body (Sub.lift 1 rho)
    Pi impl dom cod -> do
      imp' <- safeApplySubst impl rho
      dom' <- safeApplySubst dom rho
      cod' <- safeApplySubst cod $ Sub.lift 1 rho
      lift $ pi imp' dom' cod'
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
        Var v   -> do u <- Sub.lookup v rho
                      lift $ eliminate u els'
        Def n   -> lift $ app (Def n) els'
        Meta mv -> lift $ app (Meta mv) els'
        J       -> lift $ app J els'

genericWhnf
  :: (IsTerm t, MonadTerm t m) => t -> m (Blocked t)
genericWhnf t = do
  tView <- view t
  sig <- askSignature
  case tView of
    App (Meta mv) es | Just mi <- Sig.getMetaVarBody sig mv -> do
      eliminateMeta mi es
    -- Note that here we don't want to crash if the definition is not
    -- set, since I want to be able to test non-typechecked terms.
    App (Def defName) es | Just (Function _ cs) <- Sig.getDefinition sig defName -> do
      mbT <- whnfFun defName es $ ignoreInvertible cs
      case mbT of
        Just t' -> return t'
        Nothing -> return $ NotBlocked t
    App J es0@(_ : x : _ : _ : Apply _ p : Apply _' refl' : es) -> do
    -- TODO: Verify that there will be no implicit arguments for eliminators applied to J
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

eliminateMeta
  :: (IsTerm t, MonadTerm t m) => MetaVarBody t -> [Elim t] -> m (Blocked t)
eliminateMeta mvb@(MetaVarBody n body) es = whnf =<< do
  if length es >= n
    then do
      let (esl, es') = splitAt n es
      Just args <- return $ mapM isApply esl
      -- Optimization: if the arguments are all lined up, don't touch
      -- the body.
      simple <- isSimple (n-1) args
      if simple
        then eliminate body es'
        else (`eliminate` es') =<< instantiate body args
    else do
      mvT <- metaVarBodyToTerm mvb
      eliminate mvT es
  where
    isSimple _ [] = do
      return True
    isSimple n' (arg : args') = do
      argView <- view arg
      case argView of
        App (Var v) [] | varIndex v == n' -> isSimple (n'-1) args'
        _                                 -> return False

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
matchClause (Apply impl arg : es) (VarP : patterns) = do
  matched <- matchClause es patterns -- must also check some additional constraints
  return $ (\(args, leftoverEs) -> (arg : args, leftoverEs)) <$> matched
matchClause (Apply impl arg : es) (ConP dataCon dataConPatterns : patterns) = do -- same thing here, what do we need to know about this implicit argument - we want it to be Top
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
          matchClause (map (Apply impl) dataConArgs ++ es) (dataConPatterns ++ patterns)
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
    Pi impl domain codomain ->
      join $ pi <$> nf impl <*> nf domain <*> nf codomain
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
    ("p", ("x", v "A" 3) --> (app (Var (mkVar "P" 1)) . map (Apply Term.tt) =<< sequence [v "x" 0, v "x" 0, r refl])) -->
    ("eq", join (equal <$> v "A" 4 <*> v "x" 3 <*> v "y" 2)) -->
    (app (Var (mkVar "P" 2)) . map (Apply Term.tt) =<< sequence [v "x" 4, v "y" 3, v "eq" 0])
  where
    v n ix = var $ mkVar n ix
    r = return

    infixr 9 -->
    (-->) :: (Name, m t) -> m t -> m t
    (_, type_) --> t = join $ Sub.pi_ <$> type_ <*> t

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
    (Pi impl1 domain1 codomain1, Pi impl2 domain2 codomain2) ->
      (&&) <$> ((&&) <$> synEq impl1 impl2 <*> synEq domain1 domain2)
           <*> synEq codomain1 codomain2
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
    Pi impl dom cod -> do
      mbN <- runApplySubst $ safeApplySubst cod $ Sub.strengthen 1 Sub.id
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
      let h' = case h of
            Var v -> SA.Var (SA.name (PP.render v))
            Def f -> SA.Def f
            J -> SA.J SA.noSrcLoc
            Meta mv -> SA.Var (SA.Name (SA.srcLoc mv) (PP.render mv))
      args' <- forM args $ \arg -> case arg of
        Apply impl t -> SA.Apply <$> internalToTerm impl <*> internalToTerm t
        Proj p  -> return $ SA.Proj $ pName p
      return $ SA.App h' args'

genericMetaVars :: (IsTerm t, MonadTerm t m) => Term t -> m MetaVarSet
genericMetaVars t = do
  tView <- whnfView t
  case tView of
    Lam body           -> metaVars body
    Pi impl domain codomain -> do
      impMetas <- metaVars impl
      domMetas <- metaVars domain
      codMetas <- metaVars codomain
      return . mconcat $ [impMetas, domMetas, codMetas]
    Equal type_ x y    -> mconcat <$> mapM metaVars [type_, x, y]
    App h elims        -> (<>) <$> metaVarsHead h <*> metaVars elims
    Set                -> return mempty
    Refl               -> return mempty
    Con _ elims        -> metaVars elims
  where
    metaVarsHead (Meta mv) = return $ HS.singleton mv
    metaVarsHead _         = return mempty
