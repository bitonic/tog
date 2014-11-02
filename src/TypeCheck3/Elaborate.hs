{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module TypeCheck3.Elaborate
  ( elaborate
  , ElaborateState
  , initElaborateState
  , ElabM
  ) where

import           Prelude                          hiding (mapM_, pi)

import qualified Data.Bwd                         as Bwd
import           Prelude.Extended
import qualified Syntax.Internal                  as SI
import           Term
import qualified Term.Context                     as Ctx
import qualified Term.Telescope                   as Tel
import           TypeCheck3.Common
import           TypeCheck3.Monad
import           PrettyPrint                      (($$), (//>))
import qualified PrettyPrint                      as PP

data ElaborateState t = ElaborateState

initElaborateState :: IO (ElaborateState t)
initElaborateState = return ElaborateState

type ElabM t = TC t (ElaborateState t)

-- | Pre: In @elaborate Γ τ t@, @Γ ⊢ τ : Set@.
--
--   Post: If @(t′, constrs) <- elaborate Γ τ t@, @Γ t′ : τ@, and if
--   @constr@ is solved, then @t@ is well typed and @t@ and @t′@ are
--   equivalent (clarify equivalent).
elaborate
  :: (IsTerm t) => Ctx t -> Type t -> SI.Expr -> ElabM t (Term t, Constraints t)
elaborate ctx type_ absT = atSrcLoc absT $ do
  let msg = do
        typeDoc <- prettyM type_
        let absTDoc = PP.pretty absT
        return $
          "type:" //> typeDoc $$
          "t:" //> absTDoc
  debugSection "elaborate" msg $ do
    -- Don't create this here, it might not be necessary.
    mvT <- addMetaVarInCtx ctx type_
    let waitForUnifiedType type' t = jmEq ctx type_ mvT type' t
    case absT of
      SI.Set _ -> do
        return (mvT, waitForUnifiedType set set)
      SI.Pi name synDom synCod -> do
        (dom, constrDom) <- elaborate ctx set synDom
        (cod, constrCod) <- elaborate (Ctx.Snoc ctx (name, dom)) set synCod
        t <- pi dom cod
        return (mvT, waitForUnifiedType set t <> constrDom <> constrCod)
      SI.Fun synDom synCod -> do
        elaborate ctx type_ (SI.Pi "_" synDom synCod)
      SI.Meta _ -> do
        return (mvT, mempty)
      SI.Equal synType synT1 synT2 -> do
        (type', constrType) <- elaborate ctx set synType
        (t1, constrT1) <- elaborate ctx type' synT1
        (t2, constrT2) <- elaborate ctx type' synT2
        t <- equal type' t1 t2
        return (mvT, waitForUnifiedType set t <> constrType <> constrT1 <> constrT2)
      SI.Lam name synBody -> do
        dom <- addMetaVarInCtx ctx set
        let ctx' = Ctx.Snoc ctx (name, dom)
        cod <- addMetaVarInCtx ctx' set
        (body, constrBody) <- elaborate ctx' cod synBody
        type' <- pi dom cod
        t <- lam body
        return (mvT, waitForUnifiedType type' t <> constrBody)
      SI.Refl _ -> do
        eqType <- addMetaVarInCtx ctx set
        t1 <- addMetaVarInCtx ctx eqType
        type' <- equal eqType t1 t1
        return (mvT, waitForUnifiedType type' refl)
      SI.Con dataCon synArgs -> do
        DataCon tyCon _ tyConParsTel dataConType <- getDefinition dataCon
        tyConType <- definitionType =<< getDefinition tyCon
        tyConArgs <- fillArgsWithMetas ctx tyConType
        appliedDataConType <-  Tel.discharge tyConParsTel dataConType tyConArgs
        (dataConArgs, constrDataConArgs) <- elaborateDataConArgs ctx appliedDataConType synArgs
        type' <- app (Def tyCon) $ map Apply tyConArgs
        t <- con dataCon dataConArgs
        return (mvT, waitForUnifiedType type' t <> constrDataConArgs)
      SI.App h elims -> do
        elaborateApp' ctx type_ h (Bwd.fromList elims)

-- | Takes a telescope in the form of a Pi-type and replaces all it's
-- elements with metavariables.
fillArgsWithMetas :: IsTerm t => Ctx t -> Type t -> ElabM t [Term t]
fillArgsWithMetas ctx' type' = do
  typeView <- whnfView type'
  case typeView of
    Pi dom cod -> do
      arg <- addMetaVarInCtx ctx' dom
      cod' <- instantiate_ cod arg
      (arg :) <$> fillArgsWithMetas ctx' cod'
    Set -> do
      return []
    _ -> do
      fatalError "impossible.fillArgsWithMetas: bad type for tycon"

elaborateDataConArgs
  :: (IsTerm t) => Ctx t -> Type t -> [SI.Expr] -> ElabM t ([Term t], Constraints t)
elaborateDataConArgs _ _ [] =
  return ([], mempty)
elaborateDataConArgs ctx type_ (synArg : synArgs) = do
  Pi dom cod <- whnfView type_
  (arg, constrArg) <- elaborate ctx dom synArg
  cod' <- instantiate_ cod arg
  (args, constrArgs) <- elaborateDataConArgs ctx cod' synArgs
  return (arg : args, constrArg <> constrArgs)

inferHead
  :: (IsTerm t)
  => Ctx t -> SI.Head -> ElabM t (Term t, Type t)
inferHead ctx synH = atSrcLoc synH $ case synH of
  SI.Var name -> do
    mbV <-  Ctx.lookupName name ctx
    case mbV of
      Nothing -> do
        checkError $ NameNotInScope name
      Just (v, type_) -> do
        h <- app (Var v) []
        return (h, type_)
  SI.Def name -> do
    type_ <- definitionType =<< getDefinition name
    h <- app (Def name) []
    return (h, type_)
  SI.J{} -> do
    h <- app J []
    return (h, typeOfJ)

elaborateApp'
  :: (IsTerm t)
  => Ctx t -> Type t -> SI.Head -> Bwd SI.Elim -> ElabM t (Term t, Constraints t)
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
  => Ctx t -> Type t -> SI.Head -> Bwd SI.Elim -> ElabM t (Term t, Constraints t)
elaborateApp ctx type_ h B0 = atSrcLoc h $ do
  (t, hType) <- inferHead ctx h
  mvT <- addMetaVarInCtx ctx type_
  return (mvT, jmEq ctx type_ mvT hType t)
elaborateApp ctx type_ h (elims :< SI.Apply arg) = atSrcLoc arg $ do
  dom <- addMetaVarInCtx ctx set
  -- TODO better name here
  cod <- addMetaVarInCtx (Ctx.Snoc ctx ("_", dom)) set
  typeF <- pi dom cod
  (f, constrF) <- elaborateApp' ctx typeF h elims
  (arg', constrArg) <- elaborate ctx dom arg
  type' <- instantiate_ cod arg'
  t <- eliminate f [Apply arg']
  mvT <- addMetaVarInCtx ctx type_
  return (mvT, jmEq ctx type_ mvT type' t <> constrF <> constrArg)
elaborateApp ctx type_ h (elims :< SI.Proj projName) = atSrcLoc projName $ do
  Projection projIx tyCon projTypeTel projType <- getDefinition projName
  let proj = Projection' projName projIx
  tyConType <- definitionType =<< getDefinition tyCon
  tyConArgs <- fillArgsWithMetas ctx tyConType
  typeRec <- app (Def tyCon) (map Apply tyConArgs)
  (rec_, constrRec) <- elaborateApp' ctx typeRec h elims
  type0 <- Tel.discharge projTypeTel projType tyConArgs
  Pi _ type1 <- whnfView type0
  type' <- instantiate_ type1 rec_
  t <- eliminate rec_ [Proj proj]
  mvT <- addMetaVarInCtx ctx type_
  return (mvT, jmEq ctx type_ mvT type' t <> constrRec)
