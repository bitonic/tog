{-# LANGUAGE CPP #-}
module Tog.Prelude
  ( module Prelude
#if __GLASGOW_HASKELL__ < 710
  , (Control.Applicative.<*>)
  , Control.Applicative.Applicative
  , Data.Foldable.Foldable
  , Data.Traversable.Traversable
  , Control.Applicative.pure
  , Data.Traversable.sequenceA
  , Data.Traversable.traverse
#endif
  , (!!)
  , (Control.Arrow.***)
  , (Control.Applicative.<$)
  , (Control.Applicative.<$>)
  , (Control.Monad.<=<)
  , (Data.Monoid.<>)
  , (Control.Applicative.<|>)
  , (Control.Monad.>=>)
  , Data.Bifunctor.Bifunctor(..)
  , Data.Collect.Collect(..)
  , Control.Applicative.Const(..)
  , Control.Monad.Trans.Except.ExceptT(..)
  , GHC.Generics.Generic
  , Data.Hashable.Hashable(..)
  , Data.String.IsString(..)
  , Control.Monad.Trans.Maybe.MaybeT(..)
  , Control.Monad.IO.Class.MonadIO(..)
  , Data.Monoid.Monoid(..)
  , Numeric.Natural.Natural
  , Data.Typeable.Typeable
  , Data.Either.Validation.Validation(..)
  , Control.Lens._1
  , Control.Lens._2
  , Control.Lens._3
  , Data.Foldable.any
  , Control.Monad.ap
  , Data.Maybe.catMaybes
  , Data.Ord.comparing
  , Data.Either.Validation.eitherToValidation
  , Data.List.elemIndex
  , Data.Foldable.fold
  , Data.Foldable.foldl'
  , Data.Foldable.foldlM
  , Data.Traversable.for
  , Data.Traversable.forM
  , Data.Foldable.forM_
  , Data.Maybe.fromMaybe
  , Data.List.groupBy
  , Control.Monad.guard
  , System.IO.hPutStr
  , System.IO.hPutStrLn
  , Data.List.intersperse
  , Data.Maybe.isJust
  , Data.Maybe.isNothing
  , Data.List.isPrefixOf
  , Control.Monad.join
  , length
  , Control.Monad.Trans.lift
  , Control.Monad.liftM
  , Control.Monad.mplus
  , Data.Foldable.msum
  , Control.Monad.mzero
  , Data.Function.on
  , Control.Lens.over
  , replicate
  , Control.Monad.Trans.Except.runExceptT
  , Data.List.sortBy
  , System.IO.stderr
  , strictDrop
  , strictSplitAt
  , Control.Monad.Trans.Except.throwE
  , Data.Foldable.toList
  , Debug.Trace.trace
  , traceM
  , Debug.Trace.traceShow
  , Control.Monad.unless
  , Data.Either.Validation.validationToEither
  , Control.Monad.void
  , Control.Monad.when
  , Control.Lens.makeLenses
  , Control.Lens.use
  , (Control.Lens.%=)
  , (Control.Lens..=)
  , (Control.Lens.^.)
  , Control.Lens.zoom
  , Control.Lens.Lens'
  , Control.Lens.Getter
  ) where

import Prelude hiding (replicate, (!!), length, any, pi, exp)

import qualified Control.Applicative
import qualified Control.Arrow
import qualified Control.Lens
import qualified Control.Monad
import qualified Control.Monad.IO.Class
import qualified Control.Monad.Trans
import qualified Control.Monad.Trans.Except
import qualified Control.Monad.Trans.Maybe
import qualified Data.Bifunctor
import qualified Data.Collect
import qualified Data.Either.Validation
import qualified Data.Foldable
import qualified Data.Function
import qualified Data.Hashable
import qualified Data.List
import qualified Data.Maybe
import qualified Data.Monoid
import qualified Data.Ord
import qualified Data.String
import qualified Data.Traversable
import qualified Data.Typeable
import qualified Debug.Trace
import qualified GHC.Generics
import qualified Numeric.Natural
import qualified System.IO

traceM :: (Monad m) => String -> m ()
traceM string = Debug.Trace.trace string $ return ()

length :: [a] -> Numeric.Natural.Natural
length []       = 0
length (_ : xs) = 1 + length xs

(!!) :: [a] -> Numeric.Natural.Natural -> a
(x : _ ) !! 0 = x
(_ : xs) !! n = xs !! (n - 1)
[]       !! _ = error "Prelude.Extended.!!: out of bounds"

replicate :: Numeric.Natural.Natural -> a -> [a]
replicate 0 _ = []
replicate n x = x : replicate (n-1) x

strictSplitAt :: Numeric.Natural.Natural -> [a] -> ([a], [a])
strictSplitAt 0 xs       = ([], xs)
strictSplitAt _ []       = error "strictSplitAt: list too short"
strictSplitAt n (x : xs) = let (l, r) = strictSplitAt (n-1) xs in (x : l, r)

strictDrop :: Numeric.Natural.Natural -> [a] -> [a]
strictDrop 0 xs       = xs
strictDrop _ []       = error "strictDrop: list too short"
strictDrop n (_ : xs) = strictDrop (n-1) xs
