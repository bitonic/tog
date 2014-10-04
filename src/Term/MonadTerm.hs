module Term.MonadTerm
  ( MonadTerm(askSignature)
  , TermM
  , runTermM
  ) where

import           Control.Monad.Trans.Reader       (ReaderT, runReaderT, ask)

import           Prelude.Extended
import {-# SOURCE #-} qualified Term.Signature    as Sig

class (Functor m, Applicative m, Monad m, MonadIO m) => MonadTerm t m | m -> t where
  askSignature :: m (Sig.Signature t)

newtype TermM t a = TermM (ReaderT (Sig.Signature t) IO a)
  deriving (Functor, Applicative, Monad, MonadIO)

instance MonadTerm t (TermM t) where
  askSignature = TermM ask

runTermM
  :: Sig.Signature t -> TermM t a -> IO a
runTermM sig (TermM m) = runReaderT m sig
