{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
module TypeCheck3.Elaborate
  ( -- * 'ElabEnv'
    Block
  , ElabEnv
  , initElabEnv
  , elabEnvCtx
  , elabEnvTel
  , extendEnv
  , extendEnv_
  , getOpenedDefinition
  , openDefinitionInEnv
  , openDefinitionInEnv_
  , startBlock
    -- * Elaboration
  , elaborate
  ) where

import           Control.Lens                     ((&), at, (?~))
import           Control.Monad.State              (modify)
import qualified Data.HashMap.Strict              as HMS

import           Instrumentation
import           Syntax
import           Prelude.Extended
import qualified Syntax.Abstract                  as SA
import           Term
import           TypeCheck3.Common
import           TypeCheck3.Monad
import           PrettyPrint                      (($$), (//>))
import qualified PrettyPrint                      as PP

#include "impossible.h"

-- Elaboration environment
------------------------------------------------------------------------

data Block t = Block
  { _blockCtx    :: !(Ctx t)
  , _blockOpened :: !(HMS.HashMap Name [Term t])
  }

makeLenses ''Block

instance PrettyM t (Block t) where
  prettyM (Block ctx opened) = do
    ctxDoc <- prettyM ctx
    openedDoc <- prettyM $ HMS.toList opened
    return $
      "Block" $$
      "ctx:" //> ctxDoc $$
      "opened:" //> openedDoc

data ElabEnv t = ElabEnv
  { _eeBlocks :: ![Block t]
  , _eeCtx    :: !(Ctx t)
  }

makeLenses ''ElabEnv

instance PrettyM t (ElabEnv t) where
  prettyM (ElabEnv blocks ctx) = do
    blocksDoc <- prettyM blocks
    ctxDoc <- prettyM ctx
    return $
      "ElabEnv" $$
      "blocks:" //> blocksDoc $$
      "ctx:" //> ctxDoc

initElabEnv :: Ctx t -> ElabEnv t
initElabEnv ctx = ElabEnv [Block ctx HMS.empty] C0

elabEnvCtx :: ElabEnv t -> Ctx t
elabEnvCtx (ElabEnv blocks ctx) = mconcat (map _blockCtx blocks ++ [ctx])

elabEnvTel :: ElabEnv t -> Tel t
elabEnvTel (ElabEnv blocks ctx) = mconcat $ map ctxToTel $ map _blockCtx blocks ++ [ctx]

getOpenedDefinition
  :: (IsTerm t) => Name -> TC t (ElabEnv t) s (Opened Name t, Definition Opened t)
getOpenedDefinition name = do
  env <- ask
  go (ctxLength (env^.eeCtx)) (env^.eeBlocks)
  where
    go _ [] = do
      __IMPOSSIBLE__
    go n (block : blocks) = do
      case HMS.lookup name (block^.blockOpened) of
        Nothing   -> go (n + ctxLength (block^.blockCtx)) blocks
        Just args -> do
          args' <- weaken_ n args
          sig <- askSignature
          def' <- openDefinition (sigGetDefinition sig name) args'
          return (Opened name args', def')

openDefinitionInEnv :: Name -> [Term t] -> (Opened Name t -> TC t (ElabEnv t) s a) -> TC t (ElabEnv t) s a
openDefinitionInEnv name args cont = do
  env <- ask
  -- We can open a definition only when the context is empty, and there
  -- is one block.
  case env of
    ElabEnv (block : blocks) C0 -> do
      let block' = block & blockOpened . at name ?~ args
      magnifyTC (const (ElabEnv (block' : blocks) C0)) $ cont $ Opened name args
    _ ->
      __IMPOSSIBLE__

openDefinitionInEnv_ :: (IsTerm t) => Name  -> (Opened Name t -> TC t (ElabEnv t) s a) -> TC t (ElabEnv t) s a
openDefinitionInEnv_ n cont = do
  args <- mapM var . ctxVars =<< asks elabEnvCtx
  openDefinitionInEnv n args cont

startBlock :: TC t (ElabEnv t) s a -> TC t (ElabEnv t) s a
startBlock cont = do
  ElabEnv blocks ctx <- ask
  let env' = ElabEnv (Block ctx HMS.empty : blocks) C0
  magnifyTC (const env') cont

extendEnv_ :: (Name, Type t) -> TC t (ElabEnv t) s a -> TC t (ElabEnv t) s a
extendEnv_ type_ = extendEnv (C0 :< type_)

extendEnv :: Ctx t -> TC t (ElabEnv t) s a -> TC t (ElabEnv t) s a
extendEnv ctx = magnifyTC (over eeCtx (<> ctx))

addMetaInEnv :: (IsTerm t) => Type t -> ElabM t (Term t)
addMetaInEnv type_ = do
  ctx <- asks elabEnvCtx
  addMetaInCtx ctx type_

lookupName
  :: (IsTerm t) => Name -> ElabM t (Maybe (Var, Type t))
lookupName n = do
  ctx <- asks elabEnvCtx
  ctxLookupName n ctx

-- Elaboration
------------------------------------------------------------------------

-- | Pre: In @elaborate Γ τ t@, @Γ ⊢ τ : Set@.
--
--   Post: If @(t′, constrs) <- elaborate Γ τ t@, @Γ t′ : τ@, and if
--   @constr@ is solved, then @t@ is well typed and @t@ and @t′@ are
--   equivalent (clarify equivalent).
elaborate
  :: (IsTerm t) => Type t -> SA.Expr -> TC t (ElabEnv t) s (Term t, Constraints t)
elaborate type_ absT = do
  env <- ask
  let msg = do
        envDoc <- prettyM env
        return $ "env:" //> envDoc
  debugBracket "elaborate" msg $ do
    (t, constrs) <- magnifyStateTC (const []) $ (,) <$> elaborate' type_ absT <*> get
    debug "constraints" $ PP.list <$> mapM prettyM constrs
    return (t, constrs)

type ElabM t = TC t (ElabEnv t) (Constraints t)

writeConstraint :: Constraint t -> ElabM t ()
writeConstraint con' = modify (con' :)

expect :: IsTerm t => Type t -> Type t -> Term t -> ElabM t (Term t)
expect type_ type' u = do
  t <- addMetaInEnv type_
  env <- ask
  writeConstraint $ JmEq (elabEnvCtx env) type_ t type' u
  return t

elaborate'
  :: (IsTerm t) => Type t -> SA.Expr -> ElabM t (Term t)
elaborate' type_ absT = atSrcLoc absT $ do
  let msg = do
        typeDoc <- prettyM type_
        let absTDoc = PP.pretty absT
        return $
          "type:" //> typeDoc $$
          "t:" //> absTDoc
  debugBracket "elaborate" msg $ do
    let expect_ = expect type_
    case absT of
      SA.Set _ -> do
        expect_ set set
      SA.Pi name synDom synCod -> do
        dom <- elaborate' set synDom
        cod <- extendEnv_ (name, dom) $ elaborate' set synCod
        t <- pi dom cod
        expect_ set t
      SA.Fun synDom synCod -> do
        elaborate' type_ (SA.Pi "_" synDom synCod)
      SA.Meta _ -> do
        mvT <- addMetaInEnv type_
        return mvT
      SA.Equal synType synT1 synT2 -> do
        type' <- elaborate' set synType
        t1 <- elaborate' type' synT1
        t2 <- elaborate' type' synT2
        t <- equal type' t1 t2
        expect_ set t
      SA.Lam name synBody -> do
        dom <- addMetaInEnv set
        (cod, body) <- extendEnv_ (name, dom) $ do
          cod <- addMetaInEnv set
          body <- elaborate' cod synBody
          return (cod, body)
        type' <- pi dom cod
        t <- lam body
        expect_ type' t
      SA.Refl _ -> do
        eqType <- addMetaInEnv set
        t1 <- addMetaInEnv eqType
        type' <- equal eqType t1 t1
        expect_ type' refl
      SA.Con dataCon0 synArgs -> do
        (dataCon, DataCon tyCon _ dataConType) <- getOpenedDefinition dataCon0
        tyConType <- definitionType =<< getDefinition tyCon
        tyConArgs <- fillArgsWithMetas tyConType
        appliedDataConType <- openContextual dataConType tyConArgs
        dataConArgs <- elaborateDataConArgs appliedDataConType synArgs
        type' <- def tyCon $ map Apply tyConArgs
        t <- con dataCon dataConArgs
        expect_ type' t
      SA.App h elims -> do
        elaborateApp' type_ h elims

-- | Takes a telescope in the form of a Pi-type and replaces all it's
-- elements with metavariables.
fillArgsWithMetas :: IsTerm t => Type t -> ElabM t [Term t]
fillArgsWithMetas type' = do
  typeView <- whnfView type'
  case typeView of
    Pi dom cod -> do
      arg <- addMetaInEnv dom
      cod' <- instantiate_ cod arg
      (arg :) <$> fillArgsWithMetas cod'
    Set -> do
      return []
    _ -> do
      -- The tycon must end with Set
      __IMPOSSIBLE__

elaborateDataConArgs
  :: (IsTerm t) => Type t -> [SA.Expr] -> ElabM t [Term t]
elaborateDataConArgs _ [] =
  return []
elaborateDataConArgs type_ (synArg : synArgs) = do
  Pi dom cod <- whnfView type_
  arg <- elaborate' dom synArg
  cod' <- instantiate_ cod arg
  args <- elaborateDataConArgs cod' synArgs
  return (arg : args)

inferHead
  :: (IsTerm t)
  => SA.Head -> ElabM t (Term t, Type t)
inferHead synH = atSrcLoc synH $ case synH of
  SA.Var name -> do
    mbV <- lookupName name
    case mbV of
      Nothing -> do
        checkError $ NameNotInScope name
      Just (v, type_) -> do
        h <- app (Var v) []
        return (h, type_)
  SA.Def name0 -> do
    (name, def') <- getOpenedDefinition name0
    type_ <- definitionType def'
    h <- def name []
    return (h, type_)
  SA.J{} -> do
    h <- app J []
    return (h, typeOfJ)

elaborateApp'
  :: (IsTerm t)
  => Type t -> SA.Head -> [SA.Elim] -> ElabM t (Term t)
elaborateApp' type_ h elims = do
  let msg = do
        typeDoc <- prettyM type_
        return $
          "type:" //> typeDoc $$
          "head:" //> PP.pretty h $$
          "elims:" //> PP.pretty elims
  debugBracket "elaborateApp" msg $ elaborateApp type_ h $ reverse elims

-- Note that the eliminators are in reverse order.
elaborateApp
  :: (IsTerm t)
  => Type t -> SA.Head -> [SA.Elim] -> ElabM t (Term t)
elaborateApp type_ h [] = atSrcLoc h $ do
  (t, hType) <- inferHead h
  expect type_ hType t
elaborateApp type_ h (SA.Apply arg : elims) = atSrcLoc arg $ do
  dom <- addMetaInEnv set
  -- TODO better name here
  cod <- extendEnv_ ("_", dom) $ addMetaInEnv set
  typeF <- pi dom cod
  arg' <- elaborate' dom arg
  f <- elaborateApp typeF h elims
  type' <- instantiate_ cod arg'
  t <- eliminate f [Apply arg']
  expect type_ type' t
elaborateApp type_ h (SA.Proj projName0 : elims) = atSrcLoc projName0 $ do
  (projName, Projection projIx tyCon projType) <- getOpenedDefinition projName0
  let proj  = first (`Projection'` projIx) projName
  tyConType <- definitionType =<< getDefinition tyCon
  tyConArgs <- fillArgsWithMetas tyConType
  typeRec <- def tyCon (map Apply tyConArgs)
  rec_ <- elaborateApp typeRec h elims
  type0 <- openContextual projType tyConArgs
  Pi _ type1 <- whnfView type0
  type' <- instantiate_ type1 rec_
  t <- eliminate rec_ [Proj proj]
  expect type_ type' t
