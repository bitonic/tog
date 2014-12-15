{-# LANGUAGE CPP #-}
module Tog.Prelude
  ( module Prelude
  , (!!)
  , (***)
  , (<$)
  , (<$>)
  , (<*>)
  , (<=<)
  , (<>)
  , (<|>)
  , (>=>)
  , Applicative
  , Bifunctor(..)
  , Collect(..)
  , Const(..)
  , ExceptT(..)
  , Foldable
  , Generic
  , Hashable(..)
  , IsString(..)
  , MaybeT(..)
  , MonadIO(..)
  , Monoid(..)
  , Natural
  , Traversable
  , Typeable
  , Validation(..)
  , _1
  , _2
  , _3
  , any
  , ap
  , catMaybes
  , comparing
  , eitherToValidation
  , elemIndex
  , fold
  , foldl'
  , foldlM
  , for
  , forM
  , forM_
  , fromMaybe
  , groupBy
  , guard
  , hPutStr
  , hPutStrLn
  , intersperse
  , isJust
  , isNothing
  , isPrefixOf
  , join
  , length
  , lift
  , liftM
  , mplus
  , msum
  , mzero
  , on
  , over
  , pure
  , replicate
  , runExceptT
  , sequenceA
  , sortBy
  , stderr
  , strictDrop
  , strictSplitAt
  , throwE
  , toList
  , trace
  , traceM
  , traceShow
  , traverse
  , unless
  , validationToEither
  , void
  , when
  , makeLenses
  , use
  , (%=)
  , (.=)
  , (^.)
  , zoom
  , Lens'
  , Getter
  ) where

import Prelude hiding (length, any, (!!), replicate, splitAt, abs, pi)

import Control.Applicative
import Control.Arrow hiding (first, second)
import Control.Lens
import Control.Monad hiding (forM_, msum, forM)
import Control.Monad.IO.Class
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Data.Bifunctor
import Data.Collect
import Data.Either.Validation
import Data.Foldable
import Data.Function
import Data.Hashable
import Data.List hiding (foldl', any, length, (!!), replicate, splitAt)
import Data.Maybe
import Data.Monoid
import Data.Ord
import Data.String
import Data.Traversable
import Data.Typeable
import Debug.Trace
import GHC.Generics
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
replicate 0 _ = []
replicate n x = x : replicate (n-1) x

strictSplitAt :: Natural -> [a] -> ([a], [a])
strictSplitAt 0 xs       = ([], xs)
strictSplitAt _ []       = error "strictSplitAt: list too short"
strictSplitAt n (x : xs) = let (l, r) = strictSplitAt (n-1) xs in (x : l, r)

strictDrop :: Natural -> [a] -> [a]
strictDrop 0 xs       = xs
strictDrop _ []       = error "strictDrop: list too short"
strictDrop n (_ : xs) = strictDrop (n-1) xs
