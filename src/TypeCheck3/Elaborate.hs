{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
module TypeCheck3.Elaborate
  ( elaborate
  ) where

import           Control.Monad.State              (modify)

import qualified Data.Bwd                         as Bwd
import           Prelude.Extended
import           Syntax
import qualified Syntax.Abstract                  as SA
import           Term
import qualified Term.Context                     as Ctx
import qualified Term.Telescope                   as Tel
import           TypeCheck3.Common
import           TypeCheck3.Monad
import           PrettyPrint                      (($$), (//>))
import qualified PrettyPrint                      as PP

type ElabM t = TC t (Constraints t)

-- | Pre: In @elaborate Γ τ t@, @Γ ⊢ τ : Set@.
--
--   Post: If @(t′, constrs) <- elaborate Γ τ t@, @Γ t′ : τ@, and if
--   @constr@ is solved, then @t@ is well typed and @t@ and @t′@ are
--   equivalent (clarify equivalent).
elaborate
  :: (IsTerm t) => Ctx t -> Type t -> SA.Expr -> TC t s (Term t, Constraints t)
elaborate ctx type_ absT =
  nestTC [] $ elaborate' ctx type_ absT

writeConstraint :: Constraint t -> ElabM t ()
writeConstraint con' = modify (con' :)

expect :: IsTerm t => Ctx t -> Type t -> Type t -> Term t -> ElabM t (Term t)
expect ctx type_ type' u = do
  t <- addMetaVarInCtx ctx type_
  writeConstraint $ JmEq ctx type_ t type' u
  return t

elaborate'
  :: (IsTerm t) => Ctx t -> Type t -> SA.Expr -> ElabM t (Term t)
elaborate' ctx type_ absT = atSrcLoc absT $ do
  let msg = do
        typeDoc <- prettyM type_
        let absTDoc = PP.pretty absT
        return $
          "type:" //> typeDoc $$
          "t:" //> absTDoc
  debugSection "elaborate" msg $ do
    let expect_ = expect ctx type_
    case absT of
      SA.Set _ -> do
        expect_ set set
      SA.PiImpl implName synImpl domName synDom synCod -> do
        impl <- elaborate' ctx set synImpl
        let ctx' = Ctx.Snoc ctx (implName, impl)
        dom  <- elaborate' ctx' set synDom
        cod  <- elaborate' (Ctx.Snoc ctx' (domName, dom)) set synCod
        t    <- pi impl dom cod 
        expect_ set t
      SA.Pi name synDom synCod -> do
        elaborate' ctx type_ (SA.PiImpl "_" (SA.Top (srcLoc name)) name synDom synCod)
      SA.Fun synDom synCod -> do
        elaborate' ctx type_ (SA.Pi "_" synDom synCod)
      SA.Meta _ -> do
        mvT <- addMetaVarInCtx ctx type_
        return mvT
      SA.Equal synType synT1 synT2 -> do
        type' <- elaborate' ctx set synType
        t1 <- elaborate' ctx type' synT1
        t2 <- elaborate' ctx type' synT2
        t <- equal type' t1 t2
        expect_ set t
      SA.Lam name synBody -> do
        impl <- addMetaVarInCtx ctx set
        let ctx' = Ctx.Snoc ctx ("_", impl)
        dom <- addMetaVarInCtx ctx' set
        let ctx'' = Ctx.Snoc ctx' (name, dom)
        cod <- addMetaVarInCtx ctx'' set
        body <- elaborate' ctx'' cod synBody
        type' <- pi impl dom cod
        t <- lam body
        expect_ type' t
      SA.Refl _ -> do
        eqType <- addMetaVarInCtx ctx set
        t1 <- addMetaVarInCtx ctx eqType
        type' <- equal eqType t1 t1
        expect_ type' refl
      SA.Top _ -> do 
        expect_ set top
      SA.Tt _ -> do
        expect_ top tt
      SA.Con dataCon synArgs -> do
        DataCon tyCon _ tyConParsTel dataConType <- getDefinition dataCon
        tyConType <- definitionType =<< getDefinition tyCon
        tyConArgs <- fillArgsWithMetas ctx tyConType
        appliedDataConType <-  Tel.discharge tyConParsTel dataConType tyConArgs
        dataConArgs <- elaborateDataConArgs ctx appliedDataConType synArgs
        type' <- app (Def tyCon) $ map Apply tyConArgs
        t <- con dataCon dataConArgs
        expect_ type' t
      SA.App h elims -> do
        elaborateApp' ctx type_ h (Bwd.fromList elims)

-- | Takes a telescope in the form of a Pi-type and replaces all it's
-- elements with metavariables.
fillArgsWithMetas :: IsTerm t => Ctx t -> Type t -> ElabM t [Term t]
fillArgsWithMetas ctx' type' = do
  typeView <- whnfView type'
  case typeView of
    Pi impl dom cod -> do
      arg   <- addMetaVarInCtx ctx' impl
      dom'  <- instantiate_ dom arg
      arg'  <- addMetaVarInCtx ctx' dom'
      cod'  <- instantiate_ cod arg'
      (arg:) . (arg':) <$> fillArgsWithMetas ctx' cod'
    Set -> do
      return []
    _ -> do
      fatalError "impossible.fillArgsWithMetas: bad type for tycon"

elaborateDataConArgs
  :: (IsTerm t) => Ctx t -> Type t -> [SA.Expr] -> ElabM t [Term t]
elaborateDataConArgs _ _ [] =
  return []
elaborateDataConArgs ctx type_ (synArg1 : synArg2 : synArgs) = do
  Pi impl dom cod <- whnfView type_
  arg  <- elaborate' ctx impl synArg1
  dom' <- instantiate_ dom arg
  arg' <- elaborate' ctx dom synArg2
  cod' <- instantiate_ cod arg'
  args <- elaborateDataConArgs ctx cod' synArgs
  return (arg : arg' : args)
elaborateDataConArgs _ _ (_:[]) =
  fatalError "Doesn't allow single arguments - this may be changed."

inferHead
  :: (IsTerm t)
  => Ctx t -> SA.Head -> ElabM t (Term t, Type t)
inferHead ctx synH = atSrcLoc synH $ case synH of
  SA.Var name -> do
    mbV <-  Ctx.lookupName name ctx
    case mbV of
      Nothing -> do
        checkError $ NameNotInScope name
      Just (v, type_) -> do
        h <- app (Var v) []
        return (h, type_)
  SA.Def name -> do
    type_ <- definitionType =<< getDefinition name
    h <- app (Def name) []
    return (h, type_)
  SA.J{} -> do
    h <- app J []
    return (h, typeOfJ)

elaborateApp'
  :: (IsTerm t)
  => Ctx t -> Type t -> SA.Head -> Bwd SA.Elim -> ElabM t (Term t)
elaborateApp' ctx type_ h elims = do
  let msg = do
        ctxDoc <- prettyM ctx
        typeDoc <- prettyM type_
        return $
          "ctx:" //> ctxDoc $$
          "typeDoc:" //> typeDoc $$
          "head:" //> PP.pretty h $$
          "elims:" //> PP.pretty elims
  debugBracket "elaborateApp" msg $ elaborateApp ctx type_ h elims

elaborateApp
  :: (IsTerm t)
  => Ctx t -> Type t -> SA.Head -> Bwd SA.Elim -> ElabM t (Term t)
elaborateApp ctx type_ h B0 = atSrcLoc h $ do
  (t, hType) <- inferHead ctx h
  expect ctx type_ hType t
elaborateApp ctx type_ h (elims :< SA.Apply arg) = atSrcLoc arg $ do
  dom <- addMetaVarInCtx ctx set
  -- TODO better name here
  cod <- addMetaVarInCtx (Ctx.Snoc ctx ("_", dom)) set
  typeF <- pi dom cod
  arg' <- elaborate' ctx dom arg
  f <- elaborateApp' ctx typeF h elims
  type' <- instantiate_ cod arg'
  t <- eliminate f [Apply arg']
  expect ctx type_ type' t
elaborateApp ctx type_ h (elims :< SA.Proj projName) = atSrcLoc projName $ do
  Projection projIx tyCon projTypeTel projType <- getDefinition projName
  let proj = Projection' projName projIx
  tyConType <- definitionType =<< getDefinition tyCon
  tyConArgs <- fillArgsWithMetas ctx tyConType
  typeRec <- app (Def tyCon) (map Apply tyConArgs)
  rec_ <- elaborateApp' ctx typeRec h elims
  type0 <- Tel.discharge projTypeTel projType tyConArgs
  -- TODO assert that implicit is Top
  Pi _ _ type1 <- whnfView type0
  type' <- instantiate_ type1 rec_
  t <- eliminate rec_ [Proj proj]
  expect ctx type_ type' t

