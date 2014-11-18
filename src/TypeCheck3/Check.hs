{-# LANGUAGE OverloadedStrings #-}
module TypeCheck3.Check
  ( check
  , definitionallyEqual
  , instantiateMetaVar
  ) where

import           Prelude.Extended
import           Conf
import           Syntax
import           Term
import qualified Term.Context                     as Ctx
import qualified Term.Telescope                   as Tel
import           PrettyPrint                      ((<+>), ($$), (//>), render)
import qualified PrettyPrint                      as PP
import           TypeCheck3.Monad
import           TypeCheck3.Common

-- | @check Γ t A@ checks that @t@ is of type @A@ in @Γ@, treating
-- metavariables as object variables.
check
  :: (IsTerm t)
  => Ctx t -> Term t -> Type t -> TC t s ()
check ctx t type_ = do
  let msg = do
        tDoc <- prettyM t
        typeDoc <- prettyM type_
        return $
          "t:" //> tDoc $$
          "type:" //> typeDoc
  debugSection "check" msg $ do
    tView <- whnfView t
    case tView of
      Con dataCon args -> do
        DataCon tyCon _ tyConParsTel dataConType <- getDefinition dataCon
        tyConArgs <- matchTyCon tyCon type_
        appliedDataConType <- Tel.discharge tyConParsTel dataConType tyConArgs
        checkConArgs ctx args appliedDataConType
      Refl -> do
        typeView <- whnfView type_
        case typeView of
          Equal type' t1 t2 -> do
            definitionallyEqual ctx type' t1 t2
          _ -> do
            checkError $ ExpectingEqual type_
      Lam body -> do
        (dom, cod) <- matchPi type_
        name <- getAbsName_ body
        ctx' <- extendContext ctx (name, dom)
        check ctx' body cod
      _ -> do
        type' <- infer ctx t
        definitionallyEqual ctx set type' type_

checkConArgs
  :: (IsTerm t)
  => Ctx t -> [Term t] -> Type t -> TC t s ()
checkConArgs _ [] _ = do
  return ()
checkConArgs ctx (arg : args) type_ = do
  (dom, cod) <- matchPi type_
  check ctx arg dom
  cod' <-  instantiate_ cod arg
  checkConArgs ctx args cod'

checkSpine
  :: (IsTerm t)
  => Ctx t -> Term t -> [Elim t] -> Type t -> TC t s (Type t)
checkSpine _ _ [] type_ =
  return (type_)
checkSpine ctx h (el : els) type_ = case el of
  Proj proj -> do
    (h', type') <- applyProjection proj h type_
    checkSpine ctx h' els type'
  Apply arg -> do
    (dom, cod) <- matchPi type_
    check ctx arg dom
    cod' <- instantiate_ cod arg
    h' <- eliminate h [Apply arg]
    checkSpine ctx h' els cod'

applyProjection
  :: (IsTerm t)
  => Projection
  -> Term t
  -- ^ Head
  -> Type t
  -- ^ Type of the head
  -> TC t s (Term t, Type t)
applyProjection proj h type_ = do
  Projection _ tyCon projTypeTel projType <- getDefinition $ pName proj
  h' <- eliminate h [Proj proj]
  tyConArgs <- matchTyCon tyCon type_
  appliedProjType <-  Tel.discharge projTypeTel projType tyConArgs
  appliedProjTypeView <- whnfView appliedProjType
  case appliedProjTypeView of
    Pi _ endType -> do
      endType' <- instantiate_ endType h
      return (h', endType')
    _ -> do
      doc <- prettyM appliedProjType
      fatalError $ "impossible.applyProjection: " ++ render doc

infer
  :: (IsTerm t)
  => Ctx t -> Term t -> TC t s (Type t)
infer ctx t = do
  debugBracket "infer" (prettyM t) $ do
    tView <- whnfView t
    case tView of
      Set ->
        return set
      Pi dom cod -> do
        check ctx dom set
        name <- getAbsName_ cod
        ctx' <- extendContext ctx (name, dom)
        check ctx' cod set
        return set
      App h elims -> do
        type_ <- inferHead ctx h
        h' <- app h []
        checkSpine ctx h' elims type_
      Equal type_ t1 t2 -> do
        check ctx type_ set
        check ctx t1 type_
        check ctx t2 type_
        return set
      _ -> do
        fatalError "impossible.infer: non-inferrable type."

inferHead
  :: (IsTerm t)
  => Ctx t -> Head -> TC t s (Type t)
inferHead ctx h = case h of
  Var v    -> Ctx.getVar v ctx
  Def name -> definitionType =<< getDefinition name
  J        -> return typeOfJ
  Meta mv  -> getMetaVarType mv

matchTyCon
  :: (IsTerm t) => Name -> Type t -> TC t s [Term t]
matchTyCon tyCon type_ = do
  typeView <- whnfView type_
  case typeView of
    App (Def tyCon') elims | tyCon' == tyCon -> do
      let Just tyConArgs = mapM isApply elims
      return tyConArgs
    _ -> do
      checkError $ ExpectingTyCon tyCon type_

matchPi
  :: (IsTerm t) => Type t -> TC t s (Type t, Type t)
matchPi type_ = do
  typeView <- whnfView type_
  case typeView of
    Pi dom cod -> do
      return (dom, cod)
    _ -> do
      checkError $ ExpectingPi type_

-- Definitional equality
------------------------------------------------------------------------

-- | Type-directed definitional equality.
definitionallyEqual :: (IsTerm t) => Ctx t -> Type t -> Term t -> Term t -> TC t s ()
definitionallyEqual ctx type_ t1 t2 = checkEqual (ctx, type_, t1, t2)

type CheckEqual t = (Ctx t, Type t, Term t, Term t)

checkEqual
  :: (IsTerm t)
  => CheckEqual t -> TC t s ()
checkEqual x@(_, type_, t1, t2) = do
  let msg = do
        typeDoc <- prettyM type_
        t1Doc <- prettyM t1
        t2Doc <- prettyM t2
        return $
          "type:" //> typeDoc $$
          "t1:" //> t1Doc $$
          "t2:" //> t2Doc
  debugSection "defEqual" msg $
    runCheckEqual [checkSynEq, etaExpand] compareTerms x
  where
    runCheckEqual [] finally x' = do
      finally x'
    runCheckEqual (action : actions) finally x' = do
      mbX <- action x'
      forM_ mbX $ runCheckEqual actions finally

checkSynEq :: (IsTerm t) => CheckEqual t -> TC t s (Maybe (CheckEqual t))
checkSynEq (ctx, type_, t1, t2) = do
  -- Optimization: try with a simple syntactic check first.
  t1' <- ignoreBlocking =<< whnf t1
  t2' <- ignoreBlocking =<< whnf t2
  -- TODO add option to skip this check
  eq <- synEq t1' t2'
  return $ if eq
    then Nothing
    else Just (ctx, type_, t1', t2')

etaExpand :: (IsTerm t) => CheckEqual t -> TC t s (Maybe (CheckEqual t))
etaExpand (ctx, type_, t1, t2) = do
  f <- expand
  t1' <- f t1
  t2' <- f t2
  return $ Just (ctx, type_, t1', t2')
  where
    expand = do
      typeView <- whnfView type_
      case typeView of
        App (Def tyCon) _ -> do
          tyConDef <- getDefinition tyCon
          case tyConDef of
            Constant (Record dataCon projs) _ -> return $ \t -> do
              tView <- whnfView t
              case tView of
                Con _ _ -> return t
                _       -> do
                  ts <- mapM (\p -> eliminate t [Proj p]) projs
                  con dataCon ts
            _ ->
              return return
        Pi _ codomain -> return $ \t -> do
          name <- getAbsName_ codomain
          v <- var $ boundVar name
          tView <- whnfView t
          case tView of
            Lam _ -> return t
            _     -> do t' <-  weaken_ 1 t
                        t'' <- lam =<< eliminate t' [Apply v]
                        return t''
        _ ->
          return return

compareTerms :: (IsTerm t) => CheckEqual t -> TC t s ()
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
      checkEqual (ctx, set, dom1, dom2)
      cod1' <- instantiate_ cod1 dom1
      cod2' <- instantiate_ cod2 dom1
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
        DataCon _ _ dataConTypeTel dataConType <- getDefinition dataCon
        appliedDataConType <-  Tel.discharge dataConTypeTel dataConType tyConPars
        checkEqualSpine ctx appliedDataConType Nothing (map Apply dataConArgs1) (map Apply dataConArgs2)
    (Set, Set, Set) -> do
      return ()
    (_, App h elims1, App h'' elims2) | h == h'' -> do
      hType <- inferHead ctx h
      h' <- app h []
      checkEqualSpine ctx hType (Just h') elims1 elims2
    (_, _, _) -> do
     checkError $ TermsNotEqual type_ t1 type_ t2

checkEqualSpine
  :: (IsTerm t)
  => Ctx t -> Type t -> Maybe (Term t) -> [Elim t] -> [Elim t] -> TC t s ()
checkEqualSpine _ _ _ [] [] = do
  return ()
checkEqualSpine ctx type_ mbH (elim1 : elims1) (elim2 : elims2) = do
  case (elim1, elim2) of
    (Apply arg1, Apply arg2) -> do
      (dom, cod) <- matchPi type_
      checkEqual (ctx, dom, arg1, arg2)
      cod' <-  instantiate_ cod arg1
      mbH' <- traverse (`eliminate` [Apply arg1]) mbH
      checkEqualSpine ctx cod' mbH' elims1 elims2
    (Proj proj, Proj proj') | proj == proj' -> do
      let Just h = mbH
      (h', type') <- applyProjection proj h type_
      checkEqualSpine ctx type' (Just h') elims1 elims2
    _ ->
      checkError $ SpineNotEqual type_ (elim1 : elims1) type_ (elim1 : elims2)
checkEqualSpine _ type_ _ elims1 elims2 = do
  checkError $ SpineNotEqual type_ elims1 type_ elims2

-- Safe metavar instantiation
------------------------------------------------------------------------

instantiateMetaVar
  :: (IsTerm t)
  => MetaVar -> MetaVarBody t -> TC t s ()
instantiateMetaVar mv mi = do
  t <- metaVarBodyToTerm mi
  let msg = do
        tDoc <- prettyM t
        return $
          "metavar:" //> PP.pretty mv $$
          "term:" //> tDoc
  debugBracket "instantiateMeta" msg $ do
    checkConsistency <- confCheckMetaVarConsistency <$> readConf
    when checkConsistency $ do
      mvType <- getMetaVarType mv
      let msg' err = do
            tDoc <- prettyM t
            mvTypeDoc <- prettyM mvType
            return $
               "Inconsistent meta" $$
               "metavar:" <+> PP.pretty mv $$
               "type:" //> mvTypeDoc $$
               "term:" //> tDoc $$
               "err:" //> err
      assert msg' $ check Ctx.Empty t mvType
    uncheckedInstantiateMetaVar mv mi
