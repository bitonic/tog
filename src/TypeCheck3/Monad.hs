{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
module TypeCheck3.Monad
  ( -- * Monad definition
    TC
  , TCState(..)
  , tcState
  , TCErr(..)
  , initTCState
  , runTC
  , catchTC
    -- * Operations
    -- ** Errors
  , typeError
  , assert
  , assert_
    -- ** Source location
  , atSrcLoc
    -- ** Queries
  , getDefinition
  , getOpenedDefinition
  , getMetaType
    -- ** Signature update
  , addPostulate
  , addData
  , addRecordCon
  , addTypeSig
  , addClauses
  , addProjection
  , addDataCon
  , addMeta
  , uncheckedInstantiateMeta
    -- ** State handling
  , mapTC
  , nestTC
  ) where

import qualified Control.Lens                     as L
import qualified Control.Monad.State.Class        as State

import           Prelude.Extended                 hiding (any)
import           Instrumentation
import           PrettyPrint                      ((<+>), ($$), (//>))
import qualified PrettyPrint                      as PP
import           Syntax
import           Term

-- Monad definition
------------------------------------------------------------------------

-- | The "type checking" monad.
--
-- It carries around a signature, that we can modify
-- ('modifySignature'), It also lets you track of the current location
-- in the source code.
--
-- Moreover, it lets us suspend computations waiting on a 'Meta' to
-- be instantiated, or on another suspended computation to be completed.
-- See 'ProblemId' and related functions.
newtype TC t s a = TC
  {unTC :: (TCEnv, TCState t s) -> IO (TCState t s, Either TCErr a)}
  deriving (Functor)

instance Applicative (TC t s) where
  pure  = return
  (<*>) = ap

instance Monad (TC t s) where
  return x = TC $ \(_, ts) -> return (ts, Right x)

  TC m >>= f =
    TC $ \s@(te, _) -> do
      (ts, mbX) <- m s
      case mbX of
        Right x -> unTC (f x) (te, ts)
        Left e  -> return (ts, Left e)

instance MonadIO (TC t s) where
  liftIO m = TC $ \(_, ts) -> (ts,) . Right <$> m

instance MonadTerm t (TC t s) where
  askSignature = tsSignature <$> get

catchTC
  :: TC t s a -> TC t s (Either PP.Doc a)
catchTC m = TC $ \(te, ts) -> do
  (ts', mbErr) <- unTC m (te, ts)
  return $ case mbErr of
    Left e  -> (ts', Right (Left (PP.pretty e)))
    Right x -> (ts', Right (Right x))

-- | Takes a 'TCState' and a computation on a closed context and
-- produces an error or a result with a new state.
runTC :: (IsTerm t)
      => TCState t s -> TC t s a -> IO (Either PP.Doc a, TCState t s)
runTC ts (TC m) = do
  mbErr <- m (initEnv, ts)
  return $ case mbErr of
    (ts', Left e)  -> (Left (PP.pretty e), ts')
    (ts', Right x) -> (Right x, ts')

data TCEnv = TCEnv
    { teCurrentSrcLoc  :: !SrcLoc
    }

initEnv :: TCEnv
initEnv =
  TCEnv{ teCurrentSrcLoc = noSrcLoc
       }

data TCState t s = TCState
    { tsSignature        :: !(Signature t)
    -- , tsOpened           :: !(Opened t)
    , tsState            :: !s
    } deriving (Functor)

-- | An empty state.
initTCState
  :: s -> TCState t s
initTCState s = TCState
  { tsSignature        = sigEmpty
  -- , tsOpened           = mempty
  , tsState            = s
  }

tcState :: TCState t s -> s
tcState = tsState

data TCErr
    = DocErr SrcLoc PP.Doc
    deriving (Typeable)

instance PP.Pretty TCErr where
  pretty (DocErr p s) =
    "Error at" <+> PP.pretty p <+> ":" $$
    PP.nest 2 s

instance Show TCErr where
  show = PP.render

-- Errors
------------------------------------------------------------------------

-- | Fail with an error message.
typeError :: PP.Doc -> TC t s b
typeError err = do
  printStackTrace "typeError" err
  TC $ \(te, ts) -> return (ts, Left (DocErr (teCurrentSrcLoc te) err))

assert :: (PP.Doc -> TC t s PP.Doc) -> TC t s a -> TC t s a
assert msg m = do
  mbErr <- catchTC m
  case mbErr of
    Left err -> fatalError . PP.render =<< msg err
    Right x  -> return x

assert_ :: (PP.Doc -> PP.Doc) -> TC t s a -> TC t s a
assert_ msg = assert (return . msg)

-- SrcLoc
------------------------------------------------------------------------

-- | Run some action with the given 'SrcLoc'.
atSrcLoc :: HasSrcLoc a => a -> TC t s b -> TC t s b
atSrcLoc x (TC m) = TC $ \(te, ts) -> m (te{teCurrentSrcLoc = srcLoc x}, ts)

-- Signature
------------------------------------------------------------------------

-- Queries
------------------------------------------------------------------------

getOpenedDefinition
  :: (IsTerm t) => Name -> TC t s (Opened Name t, Definition Opened t)
getOpenedDefinition n0 = do
  -- TODO change when we have actual contextual definition
  let n = Opened n0 []
  def' <- getDefinition n
  return (n, def')

-- Updates
------------------------------------------------------------------------

addPostulate :: Name -> Tel t -> Type t -> TC t s ()
addPostulate f tel type_ = do
  modifySignature $ \sig -> sigAddPostulate sig f tel type_

addData :: Name -> Tel t -> Type t -> TC t s ()
addData f tel type_ = do
  modifySignature $ \sig -> sigAddData sig f tel type_

addRecordCon :: Name -> Name -> TC t s ()
addRecordCon tyCon dataCon = do
  modifySignature $ \sig -> sigAddRecordCon sig tyCon dataCon

addTypeSig :: Name -> Tel t -> Type t -> TC t s ()
addTypeSig f tel type_ = do
  modifySignature $ \sig -> sigAddTypeSig sig f tel type_

addClauses :: Name -> Invertible t -> TC t s ()
addClauses f cs = modifySignature $ \sig -> sigAddClauses sig f cs

addProjection
  :: Projection -> Name -> Contextual t (Type t) -> TC t s ()
addProjection proj tyCon ctxtType =
  modifySignature $ \sig -> sigAddProjection sig (pName proj) (pField proj) tyCon ctxtType

addDataCon
  :: Name -> Name -> Natural -> Contextual t (Type t) -> TC t s ()
addDataCon dataCon tyCon numArgs ctxtType =
  modifySignature $ \sig -> sigAddDataCon sig dataCon tyCon numArgs ctxtType

addMeta :: (IsTerm t) => Type t -> TC t s Meta
addMeta type_ = do
  loc <- teCurrentSrcLoc <$> ask
  mv <- modify $ \ts ->
    let (mv, sig') = sigAddMeta (tsSignature ts) loc type_
    in (ts{tsSignature = sig'}, mv)
  let msg = do
        typeDoc <- prettyM type_
        return $
          "mv:" //> PP.pretty mv $$
          "type:" //> typeDoc
  debugBracket "addMeta" msg $ return mv

uncheckedInstantiateMeta :: Meta -> MetaBody t -> TC t s ()
uncheckedInstantiateMeta mv mvb =
  modifySignature $ \sig -> sigInstantiateMeta sig mv mvb

-- Opened
------------------------------------------------------------------------

-- State
------------------------------------------------------------------------

instance State.MonadState s (TC t s) where
  get = tsState <$> get
  put s = modify_ $ \ts -> ts{tsState = s}
  state f = modify $ \ts -> let (x, s) = f (tsState ts) in (ts{tsState = s}, x)

mapTC :: L.Lens' s s' -> TC t s' a -> TC t s a
mapTC l (TC m) = TC $ \(te, ts) -> do
  (ts'', x) <- m (te, L.view l <$> ts)
  return ((\s -> L.set l s (tsState ts)) <$> ts'', x)

-- | Runs an action with a different state, but with the same
-- environment and signature.
nestTC :: s' -> TC t s' a -> TC t s (a, s')
nestTC s (TC m) = TC $ \(te, ts) -> do
  (ts', mbX) <- m (te, s <$ ts)
  let ts'' = tsState ts <$ ts'
  return $ case mbX of
    Left e  -> (ts'', Left e)
    Right x -> (ts'', Right (x, tsState ts'))

-- Utils
------------------------------------------------------------------------

modify :: (TCState t s -> (TCState t s, a)) -> TC t s a
modify f = TC $ \(_, ts) ->
  let (ts', x) = f ts in return (ts', Right x)

modify_ :: (TCState t s -> TCState t s) -> TC t s ()
modify_ f = modify $ \ts -> (f ts, ())

modifySignature :: (Signature t -> Signature t) -> TC t s ()
modifySignature f = modify_ $ \ts -> ts{tsSignature = f (tsSignature ts)}

get :: TC t s (TCState t s)
get = TC $ \(_, ts) -> return (ts, Right ts)

ask :: TC t s TCEnv
ask = TC $ \(te, ts) -> return (ts, Right te)
