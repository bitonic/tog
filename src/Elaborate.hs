-- | Turns some abstract expression in a term.
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Elaborate
  ( -- * 'Env'
    Block
  , Env
  , initEnv
  , envCtx
  , envTel
  , extendEnv
  , extendEnv_
  , getOpenedDefinition
  , openDefinitionInEnv
  , openDefinitionInEnv_
  , startBlock
    -- * Elaboration
  , Constraint(..)
  , Constraints
  , elaborate
  ) where

import           Control.Lens                     ((&), at, (?~))
import           Control.Monad.State              (modify)
import qualified Data.HashMap.Strict              as HMS

import           Instrumentation
import           Names
import           TogPrelude
import qualified Abstract                         as SA
import           Term
-- import           TypeCheck3.Common  
import           Monad
import           PrettyPrint                      (($$), (//>))
import qualified PrettyPrint                      as PP

#include "impossible.h"

-- Elaboration environment
------------------------------------------------------------------------

data Block t = Block
  { _blockCtx    :: !(Ctx t)
  , _blockOpened :: !(HMS.HashMap QName [Term t])
    -- ^ Stores arguments to opened things.
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

-- | The environment we do the elaboration is a series of 'Block's plus
-- a dangling context at the end.
data Env t = Env
  { _envBlocks  :: ![Block t]
  , _envPending :: !(Ctx t)
  }

makeLenses ''Env

instance PrettyM t (Env t) where
  prettyM (Env blocks ctx) = do
    blocksDoc <- prettyM blocks
    ctxDoc <- prettyM ctx
    return $
      "Env" $$
      "blocks:" //> blocksDoc $$
      "pending:" //> ctxDoc

initEnv :: Ctx t -> Env t
initEnv ctx = Env [Block ctx HMS.empty] C0

envCtx :: Env t -> Ctx t
envCtx (Env blocks ctx) = mconcat $ reverse $ ctx : map _blockCtx blocks

envTel :: Env t -> Tel t
envTel (Env blocks ctx) = mconcat $ map ctxToTel $ reverse $ ctx : map _blockCtx blocks

getOpenedDefinition
  :: (IsTerm t) => QName -> TC t (Env t) s (Opened QName t, Definition Opened t)
getOpenedDefinition name0 = do
  args <- getOpenedArgs name0
  sig <- askSignature
  def' <- openDefinition (sigGetDefinition sig name0) args
  return (Opened name0 args, def')
  where
    -- | Get the arguments of an opened name.
    getOpenedArgs name = do
      env <- ask
      go (ctxLength (env^.envPending)) (env^.envBlocks)
      where
        go _ [] = do
          __IMPOSSIBLE__
        go n (block : blocks) = do
          case HMS.lookup name (block^.blockOpened) of
            Nothing   -> go (n + ctxLength (block^.blockCtx)) blocks
            Just args -> weaken_ n args

-- | Open a definition with the given arguments.  Must be done in an
-- empty 'envPending'.
openDefinitionInEnv
  :: QName -> [Term t] -> (Opened QName t -> TC t (Env t) s a)
  -> TC t (Env t) s a
openDefinitionInEnv name args cont = do
  env <- ask
  -- We can open a definition only when the context is empty, and there
  -- is one block.
  case env of
    Env (block : blocks) C0 -> do
      let block' = block & blockOpened . at name ?~ args
      magnifyTC (const (Env (block' : blocks) C0)) $ cont $ Opened name args
    _ ->
      __IMPOSSIBLE__

-- | Open a definition using the arguments variables in 'elabCtx' as arguments.
openDefinitionInEnv_
  :: (IsTerm t)
  => QName -> (Opened QName t -> TC t (Env t) s a)
  -> TC t (Env t) s a
openDefinitionInEnv_ n cont = do
  args <- mapM var . ctxVars =<< asks envCtx
  openDefinitionInEnv n args cont

-- | Pushes a new block on 'envBlocks', using the current 'envPending'.
startBlock :: TC t (Env t) s a -> TC t (Env t) s a
startBlock cont = do
  Env blocks ctx <- ask
  let env' = Env (Block ctx HMS.empty : blocks) C0
  magnifyTC (const env') cont

extendEnv_ :: (Name, Type t) -> TC t (Env t) s a -> TC t (Env t) s a
extendEnv_ type_ = extendEnv (C0 :< type_)

-- | Appends the given 'Ctx' to the current 'envPending'.
extendEnv :: Ctx t -> TC t (Env t) s a -> TC t (Env t) s a
extendEnv ctx = magnifyTC (over envPending (<> ctx))

-- | Adds a meta-variable using the current 'envCtx' as context.
addMetaInEnv :: (IsTerm t) => Type t -> ElabM t (Term t)
addMetaInEnv type_ = do
  ctx <- asks envCtx
  addMetaInCtx ctx type_

-- | Looks up a name in the current 'envCtx'.
lookupName
  :: (IsTerm t) => Name -> ElabM t (Maybe (Var, Type t))
lookupName n = do
  ctx <- asks envCtx
  ctxLookupName n ctx

-- Elaboration
------------------------------------------------------------------------

-- Constraints
--------------

type Constraints t = [Constraint t]

data Constraint t
  = JmEq (Ctx t)
         (Type t) (Term t)
         (Type t) (Term t)

instance PrettyM t (Constraint t) where
  prettyM c = case c of
    JmEq ctx type1 t1 type2 t2 -> do
      ctxDoc <- prettyM ctx
      type1Doc <- prettyM type1
      t1Doc <- prettyM t1
      type2Doc <- prettyM type2
      t2Doc <- prettyM t2
      return $
        "JmEq" $$
        "ctx:" //> ctxDoc $$
        "t:" //> t1Doc $$
        "A:" //> type1Doc $$
        "u:" //> t2Doc $$
        "B:" //> type2Doc

-- | Pre: In @elaborate Γ τ t@, @Γ ⊢ τ : Set@.
--
--   Post: If @(t′, constrs) <- elaborate Γ τ t@, @Γ t′ : τ@, and if
--   @constr@ is solved, then @t@ is well typed and @t@ and @t′@ are
--   equivalent (clarify equivalent).
elaborate
  :: (IsTerm t) => Type t -> SA.Expr -> TC t (Env t) s (Term t, Constraints t)
elaborate type_ absT = do
  env <- ask
  let msg = do
        envDoc <- prettyM env
        return $ "env:" //> envDoc
  debugBracket "elaborate" msg $ do
    (t, constrs) <- magnifyStateTC (const []) $ (,) <$> elaborate' type_ absT <*> get
    debug "constraints" $ PP.list <$> mapM prettyM constrs
    return (t, constrs)

type ElabM t = TC t (Env t) (Constraints t)

writeConstraint :: Constraint t -> ElabM t ()
writeConstraint con' = modify (con' :)

expect :: IsTerm t => Type t -> Type t -> Term t -> ElabM t (Term t)
expect type_ type' u = do
  t <- addMetaInEnv type_
  env <- ask
  writeConstraint $ JmEq (envCtx env) type_ t type' u
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
        -- We have already scope checked
        __IMPOSSIBLE__
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

