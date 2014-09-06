{-# LANGUAGE OverloadedStrings #-}
-- TODO add options that are present in TypeCheck
module TypeCheck2.Elaborate (checkDecl, check, typeCheckProblem) where

import           Prelude                          hiding (abs, pi)

import           Control.Monad.Trans.Except       (ExceptT(ExceptT), runExceptT)
import           Control.Monad.Trans.Maybe        (MaybeT(MaybeT), runMaybeT)
import qualified Data.HashMap.Strict              as HMS
import qualified Data.HashSet                     as HS
import qualified Data.Map.Strict                  as Map
import           Data.Proxy                       (Proxy(Proxy))
import qualified Data.Set                         as Set

import           Prelude.Extended
import           Syntax.Internal                  (Name, MetaVar)
import qualified Syntax.Internal                  as A
import           Term
import           Term.Context                     (Ctx)
import qualified Term.Context                     as Ctx
import           Term.Impl
import qualified Term.Signature                   as Sig
import qualified Term.Telescope                   as Tel
import           PrettyPrint                      (($$), (<+>), (//>), render)
import qualified PrettyPrint                      as PP
import           TypeCheck2.Monad
import qualified TypeCheck2.Core                  as Core
import           TypeCheck2.Common

check
  :: (IsTerm t)
  => Ctx t -> A.Expr -> Type t -> TC' t (Term t)
check ctx synT type_ = atSrcLoc synT $ do
 let msg = do
       typeDoc <- prettyTermTC type_
       return $
         "*** check" $$
         "term:" //> PP.pretty synT $$
         "type:" //> typeDoc
 debugBracket msg $ do
   t <- case synT of
     A.Con dataCon synArgs -> do
       DataCon tyCon tyConParsTel dataConType <- getDefinition dataCon
       tyConArgs <- matchTyCon tyCon ctx type_
       appliedDataConType <- liftTermM $ Tel.substs tyConParsTel dataConType tyConArgs
       dataConArgs <- checkConArgs ctx synArgs appliedDataConType
       conTC dataCon dataConArgs
     A.Refl _ -> do
       (type', t1, t2) <- matchEqual ctx type_
       checkEqualHomo ctx type' t1 t2
       return refl
     A.Meta _ ->
       addMetaVarInCtx ctx type_
     A.Lam name synBody -> do
       (dom, cod) <- matchPi ctx type_
       ctx' <- extendContext ctx (name, dom)
       body <- check ctx' synBody cod
       lamTC body
     _ -> do
       (t, type') <- infer ctx synT
       checkEqualHomo ctx set type' type_
       return t
   debug $ do
     tDoc <- prettyTermTC t
     return $ "** Checked type:" //> tDoc
   return t

checkConArgs
  :: (IsTerm t)
  => Ctx t -> [A.Expr] -> Type t -> TC' t [t]
checkConArgs _ [] _ = do
  return []
checkConArgs ctx (synArg : synArgs) type_ = atSrcLoc synArg $ do
  (dom, cod) <- matchPi ctx type_
  arg <- check ctx synArg dom
  cod' <- liftTermM $ instantiate cod arg
  (arg :) <$> checkConArgs ctx synArgs cod'

checkSpine
  :: (IsTerm t)
  => Ctx t -> Term t -> [A.Elim] -> Type t -> TC' t (Term t, Type t)
checkSpine _ h [] type_ =
  return (h, type_)
checkSpine ctx h (el : els) type_ = atSrcLoc el $ case el of
  A.Proj proj -> do
    (h', type') <- applyProjection proj ctx h type_
    checkSpine ctx h' els type'
  A.Apply synArg -> do
    (dom, cod) <- matchPi ctx type_
    arg <- check ctx synArg dom
    cod' <- liftTermM $ instantiate cod arg
    h' <- eliminateTC h [Apply arg]
    checkSpine ctx h' els cod'

applyProjection
  :: (IsTerm t)
  => Name
  -- ^ Name of the projection
  -> Ctx t
  -> Term t
  -- ^ Head
  -> Type t
  -- ^ Type of the head
  -> TC' t (Term t, Type t)
applyProjection proj ctx h type_ = do
  Projection projIx tyCon projTypeTel projType <- getDefinition proj
  h' <- eliminateTC h [Proj proj projIx]
  tyConArgs <- matchTyCon tyCon ctx type_
  appliedProjType <- liftTermM $ Tel.substs projTypeTel projType tyConArgs
  appliedProjTypeView <- whnfViewTC appliedProjType
  case appliedProjTypeView of
    Pi _ endType -> do
      endType' <- instantiateTC endType h
      return (h', endType')
    _ -> do
      doc <- prettyTermTC appliedProjType
      error $ "impossible.applyProjection: " ++ render doc

isType :: (IsTerm t) => Ctx t -> A.Expr -> TC' t (Type t)
isType ctx abs = check ctx abs set

infer
  :: (IsTerm t)
  => Ctx t -> A.Expr -> TC' t (Term t, Type t)
infer ctx synT = atSrcLoc synT $ do
  debugBracket_ ("*** infer" $$ PP.pretty synT) $
    case synT of
      A.Set _ ->
        return (set, set)
      A.Pi name synDomain synCodomain -> do
        domain   <- isType ctx synDomain
        ctx'     <- extendContext ctx (name, domain)
        codomain <- isType ctx' synCodomain
        t <- piTC domain codomain
        return (t, set)
      A.Fun synDomain synCodomain -> do
        infer ctx $ A.Pi "_" synDomain synCodomain
      A.App synH elims -> do
        (h, type_) <- inferHead ctx synH
        checkSpine ctx h elims type_
      A.Equal synType synX synY -> do
        type_ <- isType ctx synType
        x <- check ctx synX type_
        y <- check ctx synY type_
        t <- equalTC type_ x y
        return (t, set)
      _ -> do
        -- TODO can this branch ever happen?
        type_ <- addMetaVarInCtx ctx set
        t <- check ctx synT type_
        return (t, type_)

inferHead
  :: forall t. (IsTerm t)
  => Ctx t -> A.Head -> TC' t (Term t, Type t)
inferHead ctx synH = atSrcLoc synH $ case synH of
  A.Var name -> do
    mbV <- liftTermM $ Ctx.lookupName name ctx
    case mbV of
      Nothing -> do
        checkError $ NameNotInScope name
      Just (v, type_) -> do
        h <- appTC (Var v) []
        return (h, type_)
  A.Def name -> do
    type_ <- definitionType =<< getDefinition name
    h <- appTC (Def name) []
    return (h, type_)
  A.J{} -> do
    h <- appTC J []
    return (h, typeOfJ)

matchTyCon
  :: (IsTerm t)
  => Name -> Ctx t -> Type t -> TC' t [Term t]
matchTyCon tyCon ctx0 type_ = do
  let msg = do
        typeDoc <- prettyTermTC type_
        return $
          "*** matchTyCon" <+> PP.pretty tyCon $$
          "type:" //> typeDoc
  debugBracket msg $ do
    typeView <- whnfViewTC type_
    case typeView of
      App (Def tyCon') elims | tyCon' == tyCon -> do
        let Just tyConArgs = mapM isApply elims
        return tyConArgs
      _ -> do
        tyConType <- definitionType =<< getDefinition tyCon
        tyConArgs <- fillWithMetas ctx0 tyConType
        checkEqualHomo ctx0 set type_ =<< appTC (Def tyCon) (map Apply tyConArgs)
        return tyConArgs
  where
    fillWithMetas ctx type' = do
      typeView <- whnfViewTC type'
      case typeView of
        Pi dom cod -> do
          domName <- getAbsNameTC cod
          arg <- addMetaVarInCtx ctx dom
          ctx' <- extendContext ctx (domName, arg)
          (arg :) <$> fillWithMetas ctx' cod
        Set -> do
          return []
        _ -> do
          error "impossible.fillElimsWithMetas: bad type for tycon"

matchPi
  :: (IsTerm t)
  => Ctx t -> Type t -> TC' t (Type t, Type t)
matchPi ctx type_ = do
  let msg = do
        typeDoc <- prettyTermTC type_
        return $ "*** matchPi:" //> typeDoc
  debugBracket msg $ do
    typeView <- whnfViewTC type_
    case typeView of
      Pi dom cod -> do
        return (dom, cod)
      _ -> do
        dom <- addMetaVarInCtx ctx set
        -- TODO maybe get the right name from the caller
        ctx' <- extendContext ctx ("A", dom)
        cod <- addMetaVarInCtx ctx' set
        checkEqualHomo ctx set type_ =<< piTC dom cod
        return (dom, cod)

matchEqual
  :: (IsTerm t)
  => Ctx t -> Type t -> TC' t (Type t, Term t, Term t)
matchEqual ctx type_ = do
  let msg = do
        typeDoc <- prettyTermTC type_
        return $ "*** matchEqual:" //> typeDoc
  debugBracket msg $ do
    typeView <- whnfViewTC type_
    case typeView of
      Equal type' t1 t2 -> do
        return (type', t1, t2)
      _ -> do
        type' <- addMetaVarInCtx ctx set
        t1 <- addMetaVarInCtx ctx type'
        t2 <- addMetaVarInCtx ctx type'
        checkEqualHomo ctx set type_ =<< equalTC type' t1 t2
        return (type', t1, t2)

headType
  :: (IsTerm t)
  => Ctx t -> Head -> TC' t (Type t)
headType ctx h = case h of
  Var v   -> liftTermM $ Ctx.getVar v ctx
  Def f   -> definitionType =<< getDefinition f
  J       -> return typeOfJ
  Meta mv -> getMetaVarType mv

-- Equality
------------------------------------------------------------------------

checkEqualHomo
  :: (IsTerm t)
  => Ctx t -> Type t -> Term t -> Term t
  -> TC' t ()
checkEqualHomo ctx type_ t1 t2 = checkEqual (ctx, type_, t1, ctx, type_, t2)

type CheckEqual t = (Ctx t, Type t, Term t, Ctx t, Type t, Term t)

checkEqual
  :: (IsTerm t) => CheckEqual t -> TC' t (Term t)
checkEqual (ctx1_0, type1_0, t1_0, ctx2_0, type2_0, t2_0) = do
  let msg = do
        ctxXDoc <- prettyContextTC ctx1_0
        typeXDoc <- prettyTermTC type1_0
        xDoc <- prettyTermTC t1_0
        ctxYDoc <- prettyContextTC ctx2_0
        typeYDoc <- prettyTermTC type2_0
        yDoc <- prettyTermTC t2_0
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
      [checkSynEq, etaExpand, checkMetaVars]
      compareTerms
      (ctx1_0, type1_0, t1_0, ctx2_0, type2_0, t2_0)
  where
    runCheckEqual actions0 finally args = do
      case actions0 of
        []                 -> finally args
        (action : actions) -> do
          mbArgs <- action args
          forM_ mbArgs $ runCheckEqual actions finally

checkSynEq :: (IsTerm t) => CheckEqual t -> TC' t (Maybe (CheckEqual t))
checkSynEq (ctx1, type1, t1, ctx2, type2, t2) = do
  debugBracket_ "*** Syntactic check" $ do
    -- Optimization: try with a simple syntactic check first.
    t1' <- ignoreBlockingTC =<< whnfTC t1
    t2' <- ignoreBlockingTC =<< whnfTC t2
    -- TODO add option to skip this check
    eq <- termEqTC t1' t2'
    return $ if eq
      then Nothing
      else Just (ctx1, type1, t1', ctx2, type2, t2')

etaExpand :: (IsTerm t) => CheckEqual t -> TC' t (Maybe (CheckEqual t))
etaExpand (ctx1, type1, t1, ctx2, type2, t2) = do
  debugBracket_ "*** Eta expansion" $ do
    t1' <- expandOrDont "x" type1 t1
    t2' <- expandOrDont "y" type2 t2
    return $ Just (ctx1, type1, t1', ctx2, type2, t2')
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

storeConstraint :: HS.HashSet MetaVar -> CheckEqual t -> TC' t ()
storeConstraint mvs chk = do
  void $ newProblem (WOAnyMeta mvs) $ CheckEqual chk

checkedInstantiateMetaVar :: (IsTerm t) => MetaVar -> Closed (Term t) -> TC' t ()
checkedInstantiateMetaVar mv mvT = do
  mvType <- getMetaVarType mv
  mbErr <- catchTC $ Core.check Ctx.Empty mvT mvType
  case mbErr of
    Left _err -> error "TODO checkedInstantiateMetaVar"
    Right ()  -> instantiateMetaVar mv mvT

checkMetaVars :: (IsTerm t) => CheckEqual t -> TC' t (Maybe (CheckEqual t))
checkMetaVars (ctx1, type1, t1, ctx2, type2, t2) = do
  blockedT1 <- whnfTC t1
  t1' <- ignoreBlockingTC blockedT1
  blockedT2 <- whnfTC t2
  t2' <- ignoreBlockingTC blockedT2
  let syntacticEqualityOrPostpone mvs = do
        t1'' <- nfTC t1'
        t2'' <- nfTC t2'
        eq <- liftTermM $ termEq t1'' t2''
        unless eq $ do
          debug_ $ "*** Both sides blocked, waiting for" <+> PP.pretty (HS.toList mvs)
          storeConstraint mvs (ctx1, type1, t1'', ctx2, type2, t2'')
  case (blockedT1, blockedT2) of
    (MetaVarHead mv els1, MetaVarHead mv' els2) | mv == mv' -> do
      mbKills <- intersectVars els1 els2
      case mbKills of
        Nothing -> do
          syntacticEqualityOrPostpone $ HS.singleton mv
        Just kills -> do
          checkedInstantiateMetaVar mv =<< killArgs mv kills
      return Nothing
    (MetaVarHead mv elims, _) -> do
      metaAssign ctx1 type1 mv elims t2
      return Nothing
    (_, MetaVarHead mv elims) -> do
      metaAssign ctx2 type2 mv elims t1
      return Nothing
    (BlockedOn mvs1 _ _, BlockedOn mvs2 _ _) -> do
      -- Both blocked, and we already checked for syntactic equality,
      -- let's try syntactic equality when normalized.
      syntacticEqualityOrPostpone (mvs1 <> mvs2)
      return Nothing
    (BlockedOn mvs f elims, _) -> do
      checkEqualBlockedOn ctx1 type1 mvs f elims ctx2 type2 t2
      return Nothing
    (_, BlockedOn mvs f elims) -> do
      checkEqualBlockedOn ctx2 type2 mvs f elims ctx1 type1 t1
      return Nothing
    (NotBlocked _, NotBlocked _) -> do
      return $ Just (ctx1, type1, t1', ctx2, type2, t2')

-- | @intersectVars us vs@ checks whether all relevant elements in @us@
--   and @vs@ are variables, and if yes, returns a prune list which says
--   @True@ for arguments which are different and can be pruned.
intersectVars :: (IsTerm t) => [Elim t] -> [Elim t] -> TC' t (Maybe [Named Bool])
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

killArgs :: (IsTerm t) => MetaVar -> [Named Bool] -> TC' t (Closed (Term t))
killArgs newMv kills = do
  let vs = reverse [ V (Named n ix)
                   | (ix, Named n kill) <- zip [0..] (reverse kills), not kill
                   ]
  body <- metaVarTC newMv . map Apply =<< mapM varTC vs
  foldl' (\body' _ -> lamTC =<< body') (return body) kills

checkEqualBlockedOn
  :: forall t.
     (IsTerm t)
  => Ctx t -> Type t -> HS.HashSet MetaVar -> BlockedHead -> [Elim t]
  -> Ctx t -> Type t -> Term t
  -> TC' t ()
checkEqualBlockedOn ctx1 type1 mvs bh elims1 ctx2 type2 t2 = do
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
                equalSpine (Def fun1) ctx1 elims1 ctx2 elims2
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
                        checkEqual (ctx1, type1, t1, ctx2, type2, t2)
                      else do
                        debug_ $ "** Couldn't match constructor"
                        fallback t1
                  Just _ -> do
                    checkError $ TermsNotEqual type1 t1 type2 t2
  where
    fallback t1 = storeConstraint mvs (ctx1, type1, t1, ctx2, type2, t2)

    matchPats :: [Pattern] -> [Elim t] -> TC' t Bool
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

    matchPat :: Name -> [Pattern] -> Elim t -> TC' t Bool
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
  -> TC' t (Closed (Term t))
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
  :: (IsTerm t) => Ctx t -> Tel.Tel (Type t) -> TC' t [Term t]
createMvsPars _ Tel.Empty =
  return []
createMvsPars ctx (Tel.Cons (_, type') tel) = do
  mv  <- addMetaVarInCtx ctx type'
  mvs <- createMvsPars ctx =<< liftTermM (Tel.instantiate tel mv)
  return (mv : mvs)

equalSpine
  :: (IsTerm t)
  => Head -> Ctx t -> [Elim t] -> Ctx t -> [Elim t] -> TC' t ()
equalSpine h ctx1 elims1 ctx2 elims2 = do
  h1Type <- headType ctx1 h
  h2Type <- headType ctx2 h
  checkEqualSpine ctx1 h1Type h elims1 ctx2 h2Type h elims2

checkEqualApplySpine
  :: (IsTerm t)
  => Ctx t -> Type t -> [Term t]
  -> Ctx t -> Type t -> [Term t]
  -> TC' t ()
checkEqualApplySpine ctx1 type1 args1 ctx2 type2 args2 =
  checkEqualSpine' ctx1 type1 Nothing (map Apply args1) ctx2 type2 Nothing (map Apply args2)

checkEqualSpine
  :: (IsTerm t)
  => Ctx t -> Type t -> Head -> [Elim (Term t)]
  -> Ctx t -> Type t -> Head -> [Elim (Term t)]
  -> TC' t ()
checkEqualSpine ctx1 type1 h1 elims1 ctx2 type2 h2 elims2  = do
  h1' <- appTC h1 []
  h2' <- appTC h2 []
  checkEqualSpine' ctx1 type1 (Just h1') elims1 ctx2 type2 (Just h2') elims2

checkEqualSpine'
  :: (IsTerm t)
  => Ctx t -> Type t -> Maybe (Term t) -> [Elim (Term t)]
  -> Ctx t -> Type t -> Maybe (Term t) -> [Elim (Term t)]
  -> TC' t ()
checkEqualSpine' _ _ _ [] _ _ _ [] = do
  return ()
checkEqualSpine' ctx1 type1 mbH1 (elim1 : elims1) ctx2 type2 mbH2 (elim2 : elims2) = do
  let msg = do
        let prettyMbH mbH = case mbH of
              Nothing -> return "No head"
              Just h  -> prettyTermTC h
        type1Doc <- prettyTermTC type1
        h1Doc <- prettyMbH mbH1
        elims1Doc <- prettyElimsTC $ elim1 : elims1
        type2Doc <- prettyTermTC type2
        h2Doc <- prettyMbH mbH2
        elims2Doc <- prettyElimsTC $ elim2 : elims2
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
        type1View <- whnfViewTC type1
        type2View <- whnfViewTC type2
        case (type1View, type2View) of
          (Pi dom1 cod1, Pi dom2 cod2) -> do
            checkEqual (ctx1, dom1, arg1, ctx2, dom2, arg2)
            cod1' <- liftTermM $ instantiate cod1 arg1
            mbH1' <- traverse (`eliminateTC` [Apply arg1]) mbH1
            cod2' <- liftTermM $ instantiate cod2 arg2
            mbH2' <- traverse (`eliminateTC` [Apply arg2]) mbH2
            checkEqualSpine' ctx1 cod1' mbH1' elims1 ctx2 cod2' mbH2' elims2
          (_, _) -> do
            type1Doc <- prettyTermTC type1
            type2Doc <- prettyTermTC type2
            error $ "impossible.checkEqualSpine: Expected function type\n" ++ render type1Doc ++ "\n" ++ render type2Doc
      (Proj proj projIx, Proj proj' projIx') | proj == proj' && projIx == projIx' ->
          case (mbH1, mbH2) of
            (Just h1, Just h2) -> do
              -- TODO do not use applyProjection, since it might still
              -- instantiate the type while we want to assert that the
              -- type is indeed typecon-headed.
              (h1', type1') <- applyProjection proj ctx1 h1 type1
              (h2', type2') <- applyProjection proj ctx2 h2 type2
              checkEqualSpine' ctx1 type1' (Just h1') elims1 ctx2 type2' (Just h2') elims2
            _ ->
              error $ "impossible.checkEqualSpine: got projection but no head."
      _ ->
        checkError $ SpineNotEqual type1 (elim1 : elims1) type2 (elim1 : elims2)
checkEqualSpine' _ type1 _ elims1 _ type2 _ elims2 = do
  checkError $ SpineNotEqual type1 elims1 type2 elims2

metaAssign
  :: forall t. (IsTerm t)
  => Ctx t -> Type t -> MetaVar -> [Elim (Term t)] -> Term t
  -> TC' t ()
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
          checkEqual (ctx0, type0, mvT', ctx0, type0, t0)
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
                storeConstraint mvs (ctx, type_, mvT, ctx, type_, t)
              Just mvT -> do
                mvT' <- eliminateTC mvT elims'
                checkEqual (ctx, type_, mvT', ctx, type_, t')
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
                -- Check that the type to instantiate has the right
                -- type.  This might not be the case since we've kept
                -- two contexts around...
                checkedInstantiateMetaVar mv t'
              TTMetaVars mvs -> do
                debug_ ("** Inversion blocked on" //> PP.pretty (HS.toList mvs))
                mvT <- metaVarTC mv elims
                storeConstraint mvs (ctx, type_, mvT, ctx, type_, t)
              TTFail v ->
                checkError $ FreeVariableInEquatedTerm mv elims t v

-- | The term must be in normal form.
--
-- Returns the pruned term.
pruneTerm
    :: (IsTerm t)
    => Set.Set Var                -- ^ allowed vars
    -> Term t
    -> TC' t (Term t)
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
    :: forall t.
       (IsTerm t)
    => Set.Set Var           -- ^ allowed vars
    -> MetaVar
    -> [Elim (Term t)]       -- ^ Arguments to the metavariable
    -> TC' t (Maybe (Closed (Term t)))
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
      :: Type t -> [Bool] -> TC' t (Tel.Tel (Type t), Type t, [Named Bool])
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
  => Set.Set Var -> Term t -> TC' t (Maybe Bool)
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
  :: (IsTerm t) => InvertMeta t -> TC' t PP.Doc
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
  :: forall t.
     (IsTerm t)
  => [Elim (Term t)]
  -> TC' t (TermTraverse () (InvertMeta t))
invertMeta elims0 = case mapM isApply elims0 of
    -- First we build up a list of variables representing the bound
    -- arguments in the metavar body.
    Just args0 -> go args0 $ reverse [V (Named "_" ix) | (ix, _) <- zip [0..] args0]
    Nothing    -> return $ TTFail ()
  where
    -- Then we try to invert passing pairs of arguments to the
    -- metavariable and bound arguments of the body of the
    -- metavariable.
    go :: [Term t] -> [Var] -> TC' t (TermTraverse () (InvertMeta t))
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
    checkArgs :: [(Term t, Term t)] -> TC' t (TermTraverse () [(Var, Term t)])
    checkArgs xs = do
      res <- mapM (uncurry checkArg) xs
      return $ concat <$> sequenceA res

    checkArg
      :: Term t
      -- ^ Term outside (argument to the metavar)
      -> Term t
      -- ^ Term inside (corresponding bound variable)
      -> TC' t (TermTraverse () [(Var, Term t)])
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
  :: forall t.
     (IsTerm t)
  => InvertMeta t -> Term t
  -> TC' t (TermTraverse Var (Closed (Term t)))
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
lambdaAbstract :: (IsTerm t) => Int -> Term t -> TC' t (Term t)
lambdaAbstract n t | n <= 0 = return t
lambdaAbstract n t = (lamTC <=< lambdaAbstract (n - 1)) t

applyInvertMetaSubst
  :: forall t. (IsTerm t)
  => [(Var, Term t)]
  -- ^ Inversion from variables outside to terms inside
  -> Term t
  -- ^ Term outside
  -> TC' t (TermTraverse Var (Term t))
  -- ^ Either we fail with a variable that isn't present in the
  -- substitution, or we return a new term.
applyInvertMetaSubst sub t0 =
  flip go t0 $ \v -> return $ maybe (Left v) Right (lookup v sub)
  where
    lift' :: (Var -> TC' t (Either Var (Term t)))
          -> (Var -> TC' t (Either Var (Term t)))
    lift' f v0 = case strengthenVar_ 1 v0 of
      Nothing ->
        Right <$> varTC v0
      Just v -> do
        e <- f v
        case e of
          Left v' -> return $ Left v'
          Right t -> Right <$> (liftTermM (weaken_ 1 t))

    go :: (Var -> TC' t (Either Var (Term t))) -> Term t -> TC' t (TermTraverse Var t)
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
  -> TC' t (Ctx t, [Elim t], t -> TermM t)
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
  -> TC' t (Tel.Tel t, t -> TermM t)
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
  :: (IsTerm t) => [Elim t] -> TC' t (Maybe (Var, Name))
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

etaContractElim :: (IsTerm t) => Elim t -> TC' t (Elim t)
etaContractElim (Apply t)  = Apply <$> etaContract t
etaContractElim (Proj n f) = return $ Proj n f

etaContract :: (IsTerm t) => t -> TC' t t
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

compareTerms :: (IsTerm t) => CheckEqual t -> TC' t ()
compareTerms (ctx1, type1, t1, ctx2, type2, t2) = do
  type1View <- whnfViewTC type1
  t1View <- whnfViewTC t1
  type2View <- whnfViewTC type2
  t2View <- whnfViewTC t2
  let mkVar n ix = varTC $ V $ named n ix
  case (type1View, t1View, type2View, t2View) of
    -- Note that here we rely on canonical terms to have canonical
    -- types, and on the terms to be eta-expanded.
    (Pi dom1 cod1, Lam body1, Pi dom2 cod2, Lam body2) -> do
      -- TODO there is a bit of duplication between here and expansion.
      name1 <- getAbsNameTC body1
      name2 <- getAbsNameTC body2
      ctx1' <- extendContext ctx1 (name1, dom1)
      ctx2' <- extendContext ctx2 (name2, dom2)
      checkEqual (ctx1', cod1, body1, ctx2', cod2, body2)
    (Set, Pi dom1 cod1, Set, Pi dom2 cod2) -> do
      -- Pi : (A : Set) -> (A -> Set) -> Set
      piType <- do
        av <- mkVar "A" 0
        b <- piTC av set
        piTC set =<< piTC b set
      cod1' <- lamTC cod1
      cod2' <- lamTC cod2
      checkEqualApplySpine ctx1 piType [dom1, cod1'] ctx2 piType [dom2, cod2']
    (Set, Equal type1' l1 r1, Set, Equal type2' l2 r2) -> do
      -- _==_ : (A : Set) -> A -> A -> Set
      equalType_ <- do
        xv <- mkVar "A" 0
        yv <- mkVar "A" 1
        piTC set =<< piTC xv =<< piTC yv set
      checkEqualApplySpine ctx1 equalType_ [type1', l1, r1] ctx2 equalType_ [type2', l2, r2]
    (Equal _ _ _, Refl, Equal _ _ _, Refl) -> do
      return ()
    ( App (Def _) tyConPars10, Con dataCon dataConArgs1,
      App (Def _) tyConPars20, Con dataCon' dataConArgs2
      ) | dataCon == dataCon' -> do
       let Just tyConPars1 = mapM isApply tyConPars10
       let Just tyConPars2 = mapM isApply tyConPars20
       DataCon _ dataConTypeTel dataConType <- getDefinition dataCon
       appliedDataConType1 <- liftTermM $ Tel.substs dataConTypeTel dataConType tyConPars1
       appliedDataConType2 <- liftTermM $ Tel.substs dataConTypeTel dataConType tyConPars2
       checkEqualApplySpine ctx1 appliedDataConType1 dataConArgs1 ctx2 appliedDataConType2 dataConArgs2
    (Set, Set, Set, Set) -> do
      return ()
    (_, App h1 elims1, _, App h2 elims2) | h1 == h2 -> do
      equalSpine h1 ctx1 elims1 ctx2 elims2
    (_, _, _, _) -> do
     checkError $ TermsNotEqual type1 t1 type2 t2

-- Clauses invertibility
------------------------

termHead :: (IsTerm t) => t -> TC' t (Maybe TermHead)
termHead t = do
  tView <- whnfViewTC t
  case tView of
    App (Def f) _ -> do
      fDef <- getDefinition f
      return $ case fDef of
        Constant Data{}      _ -> Just $ DefHead f
        Constant Record{}    _ -> Just $ DefHead f
        -- TODO here we can't return 'Just' because we don't know if the
        -- postulate is going to be instantiated afterwards.  Ideally we'd
        -- have a "postulate" keyword to avoid this.
        Constant Postulate{} _ -> Nothing
        _                      -> Nothing
    Con f _ ->
      return $ Just $ DefHead f
    Pi _ _ ->
      return $ Just $ PiHead
    _ ->
      return $ Nothing

checkInvertibility
  :: (IsTerm t) => [Closed (Clause t)] -> TC' t (Closed (Invertible t))
checkInvertibility = go []
  where
    go injClauses [] =
      return $ Invertible $ reverse injClauses
    go injClauses (clause@(Clause _ body) : clauses) = do
      th <- termHead body
      case th of
        Just tHead | Nothing <- lookup tHead injClauses ->
          go ((tHead, clause) : injClauses) clauses
        _ ->
          return $ NotInvertible $ reverse (map snd injClauses) ++ (clause : clauses)

typeCheckProblem
  :: (IsTerm t)
  => TypeCheckProblem t a b -> a -> StuckTC' t b
typeCheckProblem (CheckEqual x) () = do
  notStuck $ checkEqual x

-- Decls
------------------------------------------------------------------------

checkDecl :: (IsTerm t) => A.Decl -> TC' t ()
checkDecl decl = do
  debugBracket_ ("*** checkDecl" $$ PP.pretty decl) $ atSrcLoc decl $ do
    case decl of
      A.TypeSig sig      -> checkTypeSig sig
      A.DataDef d xs cs  -> checkData d xs cs
      A.RecDef d xs c fs -> checkRec d xs c fs
      A.FunDef f clauses -> checkFunDef f clauses

elaborateAndCheck
  :: (IsTerm t)
  => Ctx t -> A.Expr -> Type t -> TC' t (Term t)
elaborateAndCheck ctx synT type_ = do
  t <- check ctx synT type_
  solveProblems_
  Core.check ctx t type_
  return t

checkTypeSig :: (IsTerm t) => A.TypeSig -> TC' t ()
checkTypeSig (A.Sig name absType) = do
    type_ <- elaborateAndCheck Ctx.Empty absType set
    addConstant name Postulate type_

checkData
    :: (IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Names of parameters to the tycon.
    -> [A.TypeSig]
    -- ^ Types for the data constructors.
    -> TC' t ()
checkData tyCon tyConPars dataCons = do
    tyConType <- definitionType =<< getDefinition tyCon
    addConstant tyCon (Data []) tyConType
    (tyConPars', endType) <- unrollPiWithNames tyConType tyConPars
    Core.checkEqual (tyConPars', set, endType, set)
    appliedTyConType <- ctxAppTC (def tyCon []) tyConPars'
    mapM_ (checkConstr tyCon tyConPars' appliedTyConType) dataCons

checkConstr
    :: (IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> Ctx (Type t)
    -- ^ Ctx with the parameters of the tycon.
    -> Type t
    -- ^ Tycon applied to the parameters.
    -> A.TypeSig
    -- ^ Data constructor.
    -> TC' t ()
checkConstr tyCon tyConPars appliedTyConType (A.Sig dataCon synDataConType) = do
  atSrcLoc dataCon $ do
    dataConType <- elaborateAndCheck tyConPars synDataConType set
    (vs, endType) <- unrollPi dataConType
    appliedTyConType' <- liftTermM $ Ctx.weaken_ vs appliedTyConType
    let ctx = tyConPars Ctx.++ vs
    Core.checkEqual (ctx, set, appliedTyConType', endType)
    addDataCon dataCon tyCon (Tel.tel tyConPars) dataConType

checkRec
    :: (IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Name of the parameters to the tycon.
    -> Name
    -- ^ Name of the data constructor.
    -> [A.TypeSig]
    -- ^ Fields of the record.
    -> TC' t ()
checkRec tyCon tyConPars dataCon fields = do
    tyConType <- definitionType =<< getDefinition tyCon
    addConstant tyCon (Record dataCon []) tyConType
    (tyConPars', endType) <- unrollPiWithNames tyConType tyConPars
    Core.checkEqual (tyConPars', set, endType, set)
    fieldsTel <- checkFields tyConPars' fields
    appliedTyConType <- ctxAppTC (def tyCon []) tyConPars'
    fieldsTel' <- liftTermM $ Tel.weaken_ 1 fieldsTel
    addProjections
      tyCon tyConPars' (boundVar "_") (map A.typeSigName fields)
      fieldsTel'
    let fieldsCtx = Tel.unTel fieldsTel
    appliedTyConType' <- liftTermM $ Ctx.weaken_ fieldsCtx appliedTyConType
    addDataCon dataCon tyCon (Tel.tel tyConPars') =<< ctxPiTC fieldsCtx appliedTyConType'

checkFields
    :: forall t. (IsTerm t)
    => Ctx t -> [A.TypeSig] -> TC' t (Tel.Tel (Type t))
checkFields ctx0 = go Ctx.Empty
  where
    go :: Ctx.Ctx (Type t) -> [A.TypeSig] -> TC' t (Tel.Tel (Type t))
    go ctx [] =
        return $ Tel.tel ctx
    go ctx (A.Sig field synFieldType : fields) = do
        fieldType <- elaborateAndCheck (ctx0 Ctx.++ ctx) synFieldType set
        ctx' <- extendContext ctx (field, fieldType)
        go ctx' fields

addProjections
    :: (IsTerm t)
    => Name
    -- ^ Type constructor.
    -> Ctx (Type t)
    -- ^ A context with the parameters to the type constructor.
    -> Var
    -- ^ Variable referring to the value of type record type itself,
    -- which is the last argument of each projection ("self").  Note
    -- that this variable will have all the context above in scope.
    -> [Name]
    -- ^ Names of the remaining fields.
    -> Tel.Tel (Type t)
    -- ^ Telescope holding the types of the next fields, scoped
    -- over the types of the previous fields and the self variable.
    -> TC' t ()
addProjections tyCon tyConPars self fields0 =
    go $ zip fields0 $ map Field [0,1..]
  where
    go fields fieldTypes = case (fields, fieldTypes) of
      ([], Tel.Empty) ->
        return ()
      ((field, ix) : fields', Tel.Cons (_, fieldType) fieldTypes') -> do
        endType <- (`piTC` fieldType) =<< ctxAppTC (def tyCon []) tyConPars
        addProjection field ix tyCon (Tel.tel tyConPars) endType
        (go fields' <=< liftTermM . Tel.instantiate fieldTypes') =<< appTC (Var self) [Proj field ix]
      (_, _) -> error "impossible.addProjections: impossible: lengths do not match"

checkFunDef :: (IsTerm t) => Name -> [A.Clause] -> TC' t ()
checkFunDef fun synClauses = do
    funType <- definitionType =<< getDefinition fun
    clauses <- mapM (checkClause fun funType) synClauses
    inv <- checkInvertibility clauses
    addClauses fun inv

checkClause
  :: (IsTerm t)
  => Name -> Closed (Type t)
  -> A.Clause
  -> TC' t (Closed (Clause t))
checkClause fun funType (A.Clause synPats synClauseBody) = do
  (ctx, pats, _, clauseType) <- checkPatterns fun synPats funType
  let msg = do
        ctxDoc <- prettyContextTC ctx
        return $ "*** checkClause" $$
                 "context:" //> ctxDoc
  debugBracket msg $ do
    clauseBody <- elaborateAndCheck ctx synClauseBody clauseType
    -- This is an optimization: we want to remove as many MetaVars
    -- as possible so that we'll avoid recomputing things.
    -- TODO generalize this to everything which adds a term.
    clauseBody' <- withSignatureTermM $ \sig -> instantiateMetaVars sig clauseBody
    return $ Clause pats clauseBody'

checkPatterns
  :: (IsTerm t)
  => Name
  -> [A.Pattern]
  -> Type t
  -- ^ Type of the clause that has the given 'A.Pattern's in front.
  -> TC' t (Ctx (Type t), [Pattern], [Term t], Type t)
  -- ^ A context into the internal variables, list of internal patterns,
  -- a list of terms produced by their bindings, and the type of the
  -- clause body (scoped over the pattern variables).
checkPatterns _ [] type_ =
    return (Ctx.Empty, [], [], type_)
checkPatterns funName (synPat : synPats) type0 = atSrcLoc synPat $ do
  -- TODO this can be a soft match, like `matchPi'.  I just need to
  -- carry the context around.
  typeView <- whnfViewTC type0
  case typeView of
    Pi dom cod -> do
      (ctx, pat, patVar) <- checkPattern funName synPat dom
      cod'  <- liftTermM $ Ctx.weaken 1 ctx cod
      cod'' <- instantiateTC cod' patVar
      (ctx', pats, patsVars, bodyType) <- checkPatterns funName synPats cod''
      patVar' <- liftTermM $ Ctx.weaken_ ctx' patVar
      return (ctx Ctx.++ ctx', pat : pats, patVar' : patsVars, bodyType)
    _ -> do
      checkError $ ExpectingPi type0

checkPattern
    :: (IsTerm t)
    => Name
    -> A.Pattern
    -> Type t
    -- ^ Type of the matched thing.
    -> TC' t (Ctx (Type t), Pattern, Term t)
    -- ^ The context, the internal 'Pattern', and a 'Term' containing
    -- the term produced by it.
checkPattern funName synPat type_ = case synPat of
    A.VarP name -> do
      v <- varTC $ boundVar name
      return (Ctx.singleton name type_, VarP, v)
    A.WildP _ -> do
      v <- varTC $ boundVar "_"
      return (Ctx.singleton "_" type_, VarP, v)
    A.ConP dataCon synPats -> do
      DataCon tyCon tyConParsTel dataConType <- getDefinition dataCon
      typeConDef <- getDefinition tyCon
      case typeConDef of
        Constant (Data _)     _ -> return ()
        Constant (Record _ _) _ -> checkError $ PatternMatchOnRecord synPat tyCon
        _                       -> do doc <- prettyDefinitionTC typeConDef
                                      error $ "impossible.checkPattern " ++ render doc
      typeView <- whnfViewTC type_
      -- TODO this can be a soft match, like `matchTyCon'
      case typeView of
        App (Def tyCon') tyConArgs0 | tyCon == tyCon' -> do
          let Just tyConArgs = mapM isApply tyConArgs0
          dataConTypeNoPars <- liftTermM $ Tel.substs tyConParsTel dataConType tyConArgs
          (ctx, pats, patsVars, _) <- checkPatterns funName synPats dataConTypeNoPars
          t <- conTC dataCon patsVars
          return (ctx, ConP dataCon pats, t)
        _ -> do
          checkError $ ExpectingTyCon tyCon type_
