{-# LANGUAGE CPP #-}

module Data.Bwd (Bwd(..), fromList) where

import           Data.Foldable                    (Foldable)
import           Data.Traversable                 (Traversable)

#if __GLASGOW_HASKELL__ >= 708
import           GHC.Exts                         (IsList(..))
#else
class IsList l where
  type Item l
  fromList  :: [Item l] -> l
  toList    :: l -> [Item l]
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
