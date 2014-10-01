module Term.MonadTerm (MonadTerm(askSignature), monadTermIO) where

import           Prelude.Extended
import {-# SOURCE #-} qualified Term.Signature    as Sig

class (Functor m, Applicative m, Monad m, MonadIO m) => MonadTerm t m | m -> t where
  askSignature :: m (Sig.Signature t)

newtype M t a = M {unM :: Sig.Signature t -> IO a}

instance Functor (M t) where
  fmap = liftM

instance Applicative (M t) where
  pure = return
  (<*>) = ap

instance Monad (M t) where
  return x = M $ \_ -> return x

  M m >>= f = M $ \sig -> do
    x <- m sig
    unM (f x) sig

instance MonadIO (M t) where
  liftIO m = M $ \_ -> m

instance MonadTerm t (M t) where
  askSignature = M $ \sig -> return sig

monadTermIO
  :: Sig.Signature t -> (forall m. (MonadTerm t m) => m a) -> IO a
monadTermIO sig (M m) = m sig
