module Data.Bwd (Bwd(..), fromList) where


import           Data.Foldable                    (Foldable)
import           Data.Traversable                 (Traversable)

data Bwd a = B0 | Bwd a :< a
  deriving (Functor, Foldable, Traversable)

fromList :: [a] -> Bwd a
fromList = go . reverse
  where
    go []       = B0
    go (x : xs) = go xs :< x
