{-# LANGUAGE CPP #-}

module Data.Bwd (Bwd(..), fromList) where

import           Data.Foldable                    (Foldable)
import           Data.Traversable                 (Traversable)

#if __GLASGOW_HASKELL__ >= 708
import           GHC.Exts                         (IsList(..))
#else
import           Data.IsList
#endif

data Bwd a = B0 | Bwd a :< a
  deriving (Functor, Foldable, Traversable)

instance IsList (Bwd a) where
  type Item (Bwd a) = a

  fromList = go . reverse
    where
      go []       = B0
      go (x : xs) = go xs :< x

  toList = reverse . go
    where
      go B0        = []
      go (xs :< x) = x : go xs
