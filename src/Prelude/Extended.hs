{-# LANGUAGE CPP #-}
module Prelude.Extended
  ( Foldable
  , Traversable
  , Hashable(..)
  , (<*>)
  , Applicative
  , (<>)
  , (<$>)
  , (>=>)
  , (<=<)
  , Typeable
  , Generic
  , fromMaybe
  , pure
  , join
  , foldl'
  , liftM
  , when
  , void
  , guard
  , mzero
  , forM
  , msum
  , unless
  , first
  , forM_
  , on
  , sortBy
  , groupBy
  , isJust
  , comparing
  , traverse
  , (<$)
  , sequenceA
  , lift
  , trace
  , traceM
  , (<|>)
  , ap
  , IsString(..)
  , (***)
  , second
  , isNothing
  , Monoid(..)
  , mplus
  , any
  , MonadIO(..)
  , foldlM
  , Bwd(..)
  , toList
  , fold
  , intersperse
  , isPrefixOf
  , for
  , elemIndex
  , Natural
  , length
  , (!!)
  , module Prelude
  , replicate
  , splitAt
  , hPutStrLn
  , hPutStr
  , stderr
  ) where

import Prelude hiding (length, any, (!!), replicate, splitAt, abs, pi)
import qualified Prelude

import Control.Applicative
import Control.Arrow
import Control.Monad hiding (forM_, msum, forM)
import Control.Monad.IO.Class
import Data.Foldable
import Data.Function
import Data.Hashable
import Data.List hiding (foldl', any, length, (!!), replicate, splitAt)
import Data.Maybe
import Data.Monoid
import Data.Ord
import Data.Traversable
import Data.Typeable
import GHC.Generics
import Control.Monad.Trans
import Debug.Trace
import Data.String
import Data.Bwd
import Numeric.Natural
import System.IO

#if __GLASGOW_HASKELL__ < 708
traceM :: (Monad m) => String -> m ()
traceM string = trace string $ return ()
#endif

length :: [a] -> Natural
length []       = 0
length (_ : xs) = 1 + length xs

(!!) :: [a] -> Natural -> a
(x : _ ) !! 0 = x
(_ : xs) !! n = xs !! (n - 1)
[]       !! _ = error "Prelude.Extended.!!: out of bounds"

replicate :: Natural -> a -> [a]
replicate n = Prelude.replicate (fromIntegral n)

splitAt :: Natural -> [a] -> ([a], [a])
splitAt n = Prelude.splitAt (fromIntegral n)
