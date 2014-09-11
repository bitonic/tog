{-# LANGUAGE OverloadedStrings #-}
module TypeCheck2.Core (check, checkEqual) where

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
import           TypeCheck2.Common

check
  :: (IsTerm t)
  => Ctx t -> Term t -> Type t -> TC' t ()
check ctx t type_ = do
  let msg = do
        tDoc <- prettyTermTC t
        typeDoc <- prettyTermTC type_
        return $
          "*** Core.check" $$
          "t:" //> tDoc $$
          "type:" //> typeDoc
  debugBracket msg $ do
    tView <- whnfViewTC t
    case tView of
      Con dataCon args -> do
        DataCon tyCon tyConParsTel dataConType <- getDefinition dataCon
        tyConArgs <- matchTyCon tyCon type_
        appliedDataConType <- liftTermM $ Tel.substs tyConParsTel dataConType tyConArgs
        checkConArgs ctx args appliedDataConType
      Refl -> do
        typeView <- whnfViewTC type_
        case typeView of
          Equal type' t1 t2 -> do
            checkEqual (ctx, type', t1, t2)
          _ -> do
            checkError $ ExpectingEqual type_
      Lam body -> do
        (dom, cod) <- matchPi type_
        name <- getAbsNameTC body
        ctx' <- extendContext ctx (name, dom)
        check ctx' body cod
      _ -> do
        type' <- infer ctx t
        checkEqual (ctx, set, type', type_)

checkConArgs
  :: (IsTerm t)
  => Ctx t -> [Term t] -> Type t -> TC' t ()
checkConArgs _ [] _ = do
  return ()
checkConArgs ctx (arg : args) type_ = do
  (dom, cod) <- matchPi type_
  check ctx arg dom
  cod' <- liftTermM $ instantiate cod arg
  checkConArgs ctx args cod'

checkSpine
  :: (IsTerm t)
  => Ctx t -> Term t -> [Elim t] -> Type t -> TC' t (Type t)
checkSpine _ _ [] type_ =
  return (type_)
checkSpine ctx h (el : els) type_ = case el of
  Proj proj _ -> do
    (h', type') <- applyProjection proj h type_
    checkSpine ctx h' els type'
  Apply arg -> do
    (dom, cod) <- matchPi type_
    check ctx arg dom
    cod' <- instantiateTC cod arg
    h' <- eliminateTC h [Apply arg]
    checkSpine ctx h' els cod'

applyProjection
  :: (IsTerm t)
  => Name
  -- ^ Name of the projection
  -> Term t
  -- ^ Head
  -> Type t
  -- ^ Type of the head
  -> TC' t (Term t, Type t)
applyProjection proj h type_ = do
  Projection projIx tyCon projTypeTel projType <- getDefinition proj
  h' <- eliminateTC h [Proj proj projIx]
  tyConArgs <- matchTyCon tyCon type_
  appliedProjType <- liftTermM $ Tel.substs projTypeTel projType tyConArgs
  appliedProjTypeView <- whnfViewTC appliedProjType
  case appliedProjTypeView of
    Pi _ endType -> do
      endType' <- instantiateTC endType h
      return (h', endType')
    _ -> do
      doc <- prettyTermTC appliedProjType
      error $ "impossible.applyProjection: " ++ render doc

matchTyCon
  :: (IsTerm t) => Name -> Type t -> TC' t [Term t]
matchTyCon tyCon type_ = do
  typeView <- whnfViewTC type_
  case typeView of
    App (Def tyCon') elims | tyCon' == tyCon -> do
      let Just tyConArgs = mapM isApply elims
      return tyConArgs
    _ -> do
      checkError $ ExpectingTyCon tyCon type_

matchPi
  :: (IsTerm t) => Type t -> TC' t (Type t, Type t)
matchPi type_ = do
  typeView <- whnfViewTC type_
  case typeView of
    Pi dom cod -> do
      return (dom, cod)
    _ -> do
      checkError $ ExpectingPi type_

infer
  :: (IsTerm t)
  => Ctx t -> Term t -> TC' t (Type t)
infer ctx t = do
  tView <- viewTC t
  case tView of
    Set ->
      return set
    Pi dom cod -> do
      check ctx dom set
      name <- getAbsNameTC cod
      ctx' <- extendContext ctx (name, dom)
      check ctx' cod set
      return set
    App h elims -> do
      type_ <- inferHead ctx h
      h' <- appTC h []
      checkSpine ctx h' elims type_
    Equal type_ t1 t2 -> do
      check ctx type_ set
      check ctx t1 type_
      check ctx t2 type_
      return set
    _ -> do
      error "impossible.infer: non-inferrable type."

inferHead
  :: forall t. (IsTerm t)
  => Ctx t -> Head -> TC' t (Type t)
inferHead ctx h = case h of
  Var v    -> liftTermM $ Ctx.getVar v ctx
  Def name -> definitionType =<< getDefinition name
  J        -> return typeOfJ
  Meta mv  -> getMetaVarType mv

type CheckEqual t = (Ctx t, Type t, Term t, Term t)

checkEqual
  :: (IsTerm t)
  => CheckEqual t -> TC' t ()
checkEqual x@(ctx, type_, t1, t2) = do
  let msg = do
        ctxDoc <- prettyContextTC ctx
        typeDoc <- prettyTermTC type_
        t1Doc <- prettyTermTC t1
        t2Doc <- prettyTermTC t2
        return $
          "Core.checkEqual" $$
          "ctx:" //> ctxDoc $$
          "t1:" //> t1Doc $$
          "t2:" //> t2Doc
  debugBracket msg $ runCheckEqual [checkSynEq, etaExpand] compareTerms x
  where
    runCheckEqual [] finally x = do
      finally x
    runCheckEqual (action : actions) finally x = do
      mbX <- action x
      forM_ mbX $ runCheckEqual actions finally

checkSynEq :: (IsTerm t) => CheckEqual t -> TC' t (Maybe (CheckEqual t))
checkSynEq (ctx, type_, t1, t2) = do
  -- Optimization: try with a simple syntactic check first.
  t1' <- ignoreBlockingTC =<< whnfTC t1
  t2' <- ignoreBlockingTC =<< whnfTC t2
  -- TODO add option to skip this check
  eq <- termEqTC t1' t2'
  return $ if eq
    then Nothing
    else Just (ctx, type_, t1', t2')

etaExpand :: (IsTerm t) => CheckEqual t -> TC' t (Maybe (CheckEqual t))
etaExpand (ctx, type_, t1, t2) = do
  f <- expand
  t1' <- f t1
  t2' <- f t2
  return $ Just (ctx, type_, t1', t2')
  where
    expand = do
      typeView <- whnfViewTC type_
      case typeView of
        App (Def tyCon) _ -> do
          tyConDef <- getDefinition tyCon
          case tyConDef of
            Constant (Record dataCon projs) _ -> return $ \t -> do
              tView <- whnfViewTC t
              case tView of
                Con _ _ -> return t
                _       -> do
                  ts <- mapM (\(n, ix) -> eliminateTC t [Proj n ix]) projs
                  conTC dataCon ts
            _ ->
              return return
        Pi _ codomain -> return $ \t -> do
          name <- getAbsNameTC codomain
          v <- varTC $ boundVar name
          tView <- whnfViewTC t
          case tView of
            Lam _ -> return t
            _     -> do t' <- liftTermM $ weaken_ 1 t
                        t'' <- lamTC =<< eliminateTC t' [Apply v]
                        return t''
        _ ->
          return return

compareTerms :: (IsTerm t) => CheckEqual t -> TC' t ()
compareTerms (ctx, type_, t1, t2) = do
  typeView <- whnfViewTC type_
  t1View <- whnfViewTC t1
  t2View <- whnfViewTC t2
  case (typeView, t1View, t2View) of
    -- Note that here we rely on canonical terms to have canonical
    -- types, and on the terms to be eta-expanded.
    (Pi dom cod, Lam body1, Lam body2) -> do
      -- TODO there is a bit of duplication between here and expansion.
      name <- getAbsNameTC body1
      ctx' <- extendContext ctx (name, dom)
      checkEqual (ctx', cod, body1, body2)
    (Set, Pi dom1 cod1, Pi dom2 cod2) -> do
      checkEqual (ctx, set, dom1, dom2)
      cod1' <- instantiateTC cod1 dom1
      cod2' <- instantiateTC cod2 dom1
      checkEqual (ctx, set, cod1', cod2')
    (Set, Equal type1' l1 r1, Equal type2' l2 r2) -> do
      checkEqual (ctx, set, type1', type2')
      checkEqual (ctx, type1', l1, l2)
      checkEqual (ctx, type1', r1, r2)
    (Equal _ _ _, Refl, Refl) -> do
      return ()
    (App (Def _) tyConPars0, Con dataCon dataConArgs1, Con dataCon' dataConArgs2)
      | dataCon == dataCon' -> do
        let Just tyConPars = mapM isApply tyConPars0
        DataCon _ dataConTypeTel dataConType <- getDefinition dataCon
        appliedDataConType <- liftTermM $ Tel.substs dataConTypeTel dataConType tyConPars
        checkEqualSpine ctx appliedDataConType Nothing (map Apply dataConArgs1) (map Apply dataConArgs2)
    (Set, Set, Set) -> do
      return ()
    (_, App h elims1, App h'' elims2) | h == h'' -> do
      hType <- inferHead ctx h
      h' <- appTC h []
      checkEqualSpine ctx hType (Just h') elims1 elims2
    (_, _, _) -> do
     checkError $ TermsNotEqual type_ t1 type_ t2

checkEqualSpine
  :: (IsTerm t)
  => Ctx t -> Type t -> Maybe (Term t) -> [Elim t] -> [Elim t] -> TC' t ()
checkEqualSpine _ _ _ [] [] = do
  return ()
checkEqualSpine ctx type_ mbH (elim1 : elims1) (elim2 : elims2) = do
  case (elim1, elim2) of
    (Apply arg1, Apply arg2) -> do
      (dom, cod) <- matchPi type_
      checkEqual (ctx, dom, arg1, arg2)
      cod' <- liftTermM $ instantiate cod arg1
      mbH' <- traverse (`eliminateTC` [Apply arg1]) mbH
      checkEqualSpine ctx cod' mbH' elims1 elims2
    (Proj proj projIx, Proj proj' projIx') | proj == proj' && projIx == projIx' -> do
      let Just h = mbH
      (h', type') <- applyProjection proj h type_
      checkEqualSpine ctx type' (Just h') elims1 elims2
    _ ->
      checkError $ SpineNotEqual type_ (elim1 : elims1) type_ (elim1 : elims2)
checkEqualSpine _ type_ _ elims1 elims2 = do
  checkError $ SpineNotEqual type_ elims1 type_ elims2
