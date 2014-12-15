{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
-- | The monad that we use in elaboration, unification, and
-- type-checking in general.
module Tog.Monad
  ( -- * Monad definition
    TC
  , TC_
  , runTC
  , get
  , put
  , ask
  , asks
  , zoomTC
  , magnifyTC
  , magnifyStateTC
    -- * Operations
    -- ** Errors
  , catchTC
  , typeError
  , checkError
  , assert
  , assert_
    -- ** Source location
  , atSrcLoc
    -- ** Queries
  , getDefinition
  , getMetaType
    -- ** Signature update
  , addPostulate
  , addData
  , addRecordCon
  , addTypeSig
  , addClauses
  , addProjection
  , addDataCon
  , addModule
  , addMeta
  , addMetaInCtx
  , uncheckedInstantiateMeta
    -- * Miscellanea
  , extendContext
  , unrollPiWithNames
  , unrollPi
  ) where

import qualified Control.Lens                     as L
import           Control.Monad.State.Strict       (StateT(StateT), runStateT, MonadState(..))
import           Control.Monad.Reader             (MonadReader(..), asks)
import           Control.Monad.Except             (catchError)

import           Tog.Prelude
import           Tog.Instrumentation
import           Tog.PrettyPrint                  ((<+>), ($$), (//>))
import qualified Tog.PrettyPrint                  as PP
import           Tog.Names
import           Tog.Term
import           Tog.Error

-- Monad definition
------------------------------------------------------------------------

-- | The "type checking" monad.
--
-- It carries around a signature that we can modify, and also lets you
-- track of the current location in the source code.
--
-- Moreover, it's also a reader and state over some @r@ and @s@.
newtype TC t r s a = TC
  {unTC :: ExceptT TCErr (StateT (TCState t r s) IO) a}
  deriving (Functor, Applicative, Monad, MonadIO)

type TC_ t a = forall r s. TC t r s a

data TCErr
    = DocErr SrcLoc PP.Doc
    deriving (Typeable)

data TCState t r s = TCState
    { _tsSignature        :: !(Signature t)
    , _tsSrcLoc           :: !SrcLoc
    , _tsEnv              :: !r
    , _tsState            :: !s
    } deriving (Functor)

makeLenses ''TCState

instance Bifunctor (TCState t) where
  bimap f g = over tsEnv f . over tsState g
  first = over tsEnv
  second = over tsState

instance PP.Pretty TCErr where
  pretty (DocErr p s) =
    "Error at" <+> PP.pretty p <+> ":" $$
    PP.nest 2 s

instance Show TCErr where
  show = PP.render

instance MonadReader r (TC t r s) where
  ask = TC $ use tsEnv
  local f m = TC $ do
    oldEnv <- use tsEnv
    tsEnv %= f
    x <- unTC m
    tsEnv .= oldEnv
    return x

instance MonadState s (TC t r s) where
  get = TC $ use tsState
  put x = TC $ tsState .= x

instance (IsTerm t) => MonadTerm t (TC t r s) where
  askSignature = TC $ use tsSignature

runTC :: (IsTerm t)
      => Signature t -> r -> s -> TC t r s a
      -> IO (Either PP.Doc a, Signature t, s)
runTC sig env st m = do
  let ts = TCState sig noSrcLoc env st
  mbErr <- runStateT (runExceptT (unTC m)) ts
  return $ case mbErr of
    (Left e, ts')  -> (Left (PP.pretty e), ts'^.tsSignature, ts'^.tsState)
    (Right x, ts') -> (Right x, ts'^.tsSignature, ts'^.tsState)

zoomTC :: Lens' s a -> TC t r a c -> TC t r s c
zoomTC l m = TC $ ExceptT $ StateT $ \ts0 -> do
  (mbErr, ts1) <- runStateT (runExceptT (unTC m)) (second (L.view l) ts0)
  let ts2 = second (\x -> L.set l x (ts0^.tsState)) ts1
  return (mbErr, ts2)

magnifyTC :: (r -> a) -> TC t a s c -> TC t r s c
magnifyTC l m = TC $ ExceptT $ StateT $ \ts0 -> do
  (mbErr, ts1) <- runStateT (runExceptT (unTC m)) (first l ts0)
  let ts2 = first (const (ts0^.tsEnv)) ts1
  return (mbErr, ts2)

magnifyStateTC :: (s -> a) -> TC t r a c -> TC t r s c
magnifyStateTC l m = TC $ ExceptT $ StateT $ \ts0 -> do
  (mbErr, ts1) <- runStateT (runExceptT (unTC m)) (second l ts0)
  let ts2 = second (const (ts0^.tsState)) ts1
  return (mbErr, ts2)

-- Errors
------------------------------------------------------------------------

catchTC
  :: TC t r s a -> TC t r s (Either PP.Doc a)
catchTC m = TC $ catchError (Right <$> unTC m) $ return . Left . PP.pretty

-- | Fail with an error message.
typeError :: PP.Doc -> TC t r s b
typeError err = TC $ do
  printStackTrace "typeError" err
  loc <- use tsSrcLoc
  throwE $ DocErr loc err

checkError :: (IsTerm t) => CheckError t -> TC_ t a
checkError err = typeError =<< prettyM err

assert :: (PP.Doc -> TC t r s PP.Doc) -> TC t r s a -> TC t r s a
assert msg m = do
  mbErr <- catchTC m
  case mbErr of
    Left err -> fatalError . PP.render =<< msg err
    Right x  -> return x

assert_ :: (PP.Doc -> PP.Doc) -> TC t r s a -> TC t r s a
assert_ msg = assert (return . msg)

-- SrcLoc
------------------------------------------------------------------------

-- | Run some action with the given 'SrcLoc'.
atSrcLoc :: HasSrcLoc a => a -> TC t r s b -> TC t r s b
atSrcLoc l m = TC $ do
  oldLoc <- use tsSrcLoc
  tsSrcLoc .= srcLoc l
  x <- unTC m
  tsSrcLoc .= oldLoc
  return x

-- Signature
------------------------------------------------------------------------

addPostulate :: QName -> Tel t -> Type t -> TC t r s ()
addPostulate f tel type_ = do
  modifySignature $ \sig -> sigAddPostulate sig f tel type_

addData :: QName -> Tel t -> Type t -> TC t r s ()
addData f tel type_ = do
  modifySignature $ \sig -> sigAddData sig f tel type_

addRecordCon :: Opened QName t -> QName -> TC t r s ()
addRecordCon tyCon dataCon = do
  modifySignature $ \sig -> sigAddRecordCon sig tyCon dataCon

addTypeSig :: QName -> Tel t -> Type t -> TC t r s ()
addTypeSig f tel type_ = do
  modifySignature $ \sig -> sigAddTypeSig sig f tel type_

addClauses :: Opened QName t -> Invertible t -> TC t r s ()
addClauses f cs = modifySignature $ \sig -> sigAddClauses sig f cs

addProjection
  :: Projection -> Opened QName t -> Contextual t (Type t) -> TC t r s ()
addProjection proj tyCon ctxtType =
  modifySignature $ \sig -> sigAddProjection sig (pName proj) (pField proj) tyCon ctxtType

addDataCon
  :: QName -> Opened QName t -> Natural -> Contextual t (Type t) -> TC t r s ()
addDataCon dataCon tyCon numArgs ctxtType =
  modifySignature $ \sig -> sigAddDataCon sig dataCon tyCon numArgs ctxtType

addModule :: (IsTerm t) => QName -> Tel t -> Module t -> TC t r s ()
addModule moduleName tel names = do
  debugBracket_ "addModule" (PP.pretty moduleName) $
    modifySignature $ \sig -> sigAddModule sig moduleName tel names

addMeta :: forall t r s. (IsTerm t) => Type t -> TC t r s Meta
addMeta type_ = do
  loc <- TC $ use tsSrcLoc
  ts <- TC get
  let (mv, sig') = sigAddMeta (ts^.tsSignature) loc type_
  TC $ tsSignature .= sig'
  let msg = do
        typeDoc <- prettyM type_
        return $
          "mv:" //> PP.pretty mv $$
          "type:" //> typeDoc
  debugBracket "addMeta" msg $ return mv

addMetaInCtx
  :: (IsTerm t)
  => Ctx t -> Type t -> TC_ t (Term t)
addMetaInCtx ctx type_ = do
  type' <- ctxPi ctx type_
  mv <- addMeta type'
  ctxApp (meta mv []) ctx

uncheckedInstantiateMeta :: Meta -> MetaBody t -> TC t r s ()
uncheckedInstantiateMeta mv mvb =
  modifySignature $ \sig -> sigInstantiateMeta sig mv mvb

-- Utils
------------------------------------------------------------------------

modifySignature :: (Signature t -> Signature t) -> TC t r s ()
modifySignature f = TC $ tsSignature %= f

-- Miscellanea
------------------------------------------------------------------------

-- Miscellanea
------------------------------------------------------------------------

-- Telescope & context utils
----------------------------

-- | Useful just for debugging.
extendContext
  :: (IsTerm t, MonadTerm t m)
  => Ctx (Type t) -> (Name, Type t) -> m (Ctx (Type t))
extendContext ctx type_ = do
  let ctx' = ctx :< type_
  debug "extendContext" $ prettyM ctx'
  return ctx'

-- Unrolling Pis
----------------

-- TODO remove duplication

unrollPiWithNames
  :: (IsTerm t)
  => Type t
  -- ^ Type to unroll
  -> [Name]
  -- ^ Names to give to each parameter
  -> TC_ t (Tel (Type t), Type t)
  -- ^ A telescope with accumulated domains of the pis and the final
  -- codomain.
unrollPiWithNames type_ [] =
  return (T0, type_)
unrollPiWithNames type_ (name : names) = do
  typeView <- whnfView type_
  case typeView of
    Pi domain codomain -> do
      (ctx, endType) <- unrollPiWithNames codomain names
      return ((name, domain) :> ctx, endType)
    _ -> do
      checkError $ ExpectingPi type_

unrollPi
  :: (IsTerm t, MonadTerm t m)
  => Type t
  -- ^ Type to unroll
  -> m (Tel (Type t), Type t)
unrollPi type_ = do
  typeView <- whnfView type_
  case typeView of
    Pi domain codomain -> do
      name <- getAbsName_ codomain
      (ctx, endType) <- unrollPi codomain
      return ((name, domain) :> ctx, endType)
    _ ->
      return (T0, type_)
