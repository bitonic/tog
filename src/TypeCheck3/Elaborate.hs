{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module TypeCheck3.Elaborate
  ( elaborate
  , ElaborateState
  , initElaborateState
  , ElabM
  ) where

import           Prelude                          hiding (mapM_, pi)

import           Prelude.Extended
import qualified Syntax.Internal                  as A
import           Term
import           Term.Context                     (Ctx)
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
  :: (IsTerm t) => Ctx t -> Type t -> A.Expr -> ElabM t (Term t, Constraint t)
elaborate ctx type_ absT = atSrcLoc absT $ do
  let msg = do
        typeDoc <- prettyTermM type_
        let absTDoc = PP.pretty absT
        return $
          "*** elaborate" $$
          "type:" //> typeDoc $$
          "t:" //> absTDoc
  debugBracket msg $ do
    -- Don't create this here, it might not be necessary.
    mvT <- addMetaVarInCtx ctx type_
    let waitForUnifiedType' type' t = waitForUnifiedType ctx type_ type' mvT t
    case absT of
      A.Set _ -> do
        return (mvT, waitForUnifiedType' set set)
      A.Pi name synDom synCod -> do
        (dom, constrDom) <- elaborate ctx set synDom
        (cod, constrCod) <- elaborate (Ctx.Snoc ctx (name, dom)) set synCod
        t <- pi dom cod
        return (mvT, Conj [waitForUnifiedType' set t, constrDom, constrCod])
      A.Fun synDom synCod -> do
        elaborate ctx type_ (A.Pi "_" synDom synCod)
      A.Meta _ ->
        return (mvT, Conj [])
      A.Equal synType synT1 synT2 -> do
        (type', constrType) <- elaborate ctx set synType
        (t1, constrT1) <- elaborate ctx type' synT1
        (t2, constrT2) <- elaborate ctx type' synT2
        t <- equal type' t1 t2
        return (mvT, Conj [waitForUnifiedType' set t, constrType, constrT1, constrT2])
      A.Lam name synBody -> do
        dom <- addMetaVarInCtx ctx set
        let ctx' = Ctx.Snoc ctx (name, dom)
        cod <- addMetaVarInCtx ctx' set
        (body, constrBody) <- elaborate ctx' cod synBody
        type' <- pi dom cod
        t <- lam body
        return (mvT, Conj [waitForUnifiedType' type' t, constrBody])
      A.Refl _ -> do
        eqType <- addMetaVarInCtx ctx set
        t1 <- addMetaVarInCtx ctx eqType
        type' <- equal eqType t1 t1
        return (mvT, waitForUnifiedType' type' refl)
      A.Con dataCon synArgs -> do
        DataCon tyCon _ tyConParsTel dataConType <- getDefinition dataCon
        tyConType <- definitionType =<< getDefinition tyCon
        tyConArgs <- fillArgsWithMetas ctx tyConType
        appliedDataConType <-  Tel.substs tyConParsTel dataConType tyConArgs
        (dataConArgs, constrDataConArgs) <- elaborateDataConArgs ctx appliedDataConType synArgs
        type' <- app (Def tyCon) $ map Apply tyConArgs
        t <- con dataCon dataConArgs
        return (mvT, Conj (waitForUnifiedType' type' t : constrDataConArgs))
      A.App h elims -> do
        elaborateApp' ctx type_ h (reverse elims)

-- | Takes a telescope in the form of a Pi-type and replaces all it's
-- elements with metavariables.
fillArgsWithMetas :: IsTerm t => Ctx t -> Type t -> ElabM t [Term t]
fillArgsWithMetas ctx' type' = do
  typeView <- whnfView type'
  case typeView of
    Pi dom cod -> do
      arg <- addMetaVarInCtx ctx' dom
      cod' <- instantiate cod arg
      (arg :) <$> fillArgsWithMetas ctx' cod'
    Set -> do
      return []
    _ -> do
      fatalError "impossible.fillArgsWithMetas: bad type for tycon"

-- | Pre: In @waitForUnifiedType Γ τ σ t u@, we have
--   @Γ ⊢ τ : Set@, @Γ ⊢ σ : Set@, @Γ ⊢ t : τ@, @Γ ⊢ u : τ@.
--
--   Waits for τ and σ to be unified, then unifies t and u.
waitForUnifiedType
  :: IsTerm (Term t)
  => Ctx t
  -> Term t
  -- ^ When this type...
  -> Type t
  -- ^ ..is unified with this type...
  -> Term t
  -- ^ ..unify this term...
  -> Term t
  -- ^ ..with this term.
  -> Constraint t
waitForUnifiedType ctx type_ type' mvT t = do
  Unify ctx set type' type_ :>>: Unify ctx type_ mvT t

elaborateDataConArgs
  :: (IsTerm t) => Ctx t -> Type t -> [A.Expr] -> ElabM t ([Term t], [Constraint t])
elaborateDataConArgs _ _ [] =
  return ([], [])
elaborateDataConArgs ctx type_ (synArg : synArgs) = do
  Pi dom cod <- whnfView type_
  (arg, constrArg) <- elaborate ctx dom synArg
  cod' <- instantiate cod arg
  (args, constrArgs) <- elaborateDataConArgs ctx cod' synArgs
  return (arg : args, constrArg : constrArgs)

inferHead
  :: (IsTerm t)
  => Ctx t -> A.Head -> ElabM t (Term t, Type t)
inferHead ctx synH = atSrcLoc synH $ case synH of
  A.Var name -> do
    mbV <-  Ctx.lookupName name ctx
    case mbV of
      Nothing -> do
        checkError $ NameNotInScope name
      Just (v, type_) -> do
        h <- app (Var v) []
        return (h, type_)
  A.Def name -> do
    type_ <- definitionType =<< getDefinition name
    h <- app (Def name) []
    return (h, type_)
  A.J{} -> do
    h <- app J []
    return (h, typeOfJ)

elaborateApp'
  :: (IsTerm t)
  => Ctx t -> Type t -> A.Head -> [A.Elim] -> ElabM t (Term t, Constraint t)
elaborateApp' ctx type_ h elims = do
  let msg = do
        ctxDoc <- prettyM ctx
        typeDoc <- prettyTermM type_
        return $
          "*** elaborateApp" $$
          "ctx:" //> ctxDoc $$
          "typeDoc:" //> typeDoc $$
          "head:" //> PP.pretty h $$
          "elims:" //> PP.pretty elims
  debugBracket msg $ elaborateApp ctx type_ h elims

elaborateApp
  :: (IsTerm t)
  => Ctx t -> Type t -> A.Head -> [A.Elim] -> ElabM t (Term t, Constraint t)
elaborateApp ctx type_ h [] = atSrcLoc h $ do
  (t, hType) <- inferHead ctx h
  mvT <- addMetaVarInCtx ctx type_
  return (mvT, waitForUnifiedType ctx type_ hType mvT t)
elaborateApp ctx type_ h (A.Apply arg : elims) = atSrcLoc arg $ do
  dom <- addMetaVarInCtx ctx set
  -- TODO better name here
  cod <- addMetaVarInCtx (Ctx.Snoc ctx ("_", dom)) set
  typeF <- pi dom cod
  (f, constrF) <- elaborateApp' ctx typeF h elims
  (arg', constrArg) <- elaborate ctx dom arg
  type' <- instantiate cod arg'
  t <- eliminate f [Apply arg']
  mvT <- addMetaVarInCtx ctx type_
  return (mvT, Conj [waitForUnifiedType ctx type_ type' mvT t, constrF, constrArg])
elaborateApp ctx type_ h (A.Proj proj : elims) = atSrcLoc proj $ do
  Projection projIx tyCon projTypeTel projType <- getDefinition proj
  tyConType <- definitionType =<< getDefinition tyCon
  tyConArgs <- fillArgsWithMetas ctx tyConType
  typeRec <- app (Def tyCon) (map Apply tyConArgs)
  (rec_, constrRec) <- elaborateApp' ctx typeRec h elims
  type0 <- Tel.substs projTypeTel projType tyConArgs
  Pi _ type1 <- whnfView type0
  type' <- instantiate type1 rec_
  t <- eliminate rec_ [Proj proj projIx]
  mvT <- addMetaVarInCtx ctx type_
  return (mvT, Conj [waitForUnifiedType ctx type_ type' mvT t, constrRec])
