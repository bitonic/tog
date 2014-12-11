module Data.Collect where

import           Control.Applicative              (Applicative, pure, (<*>))
import           Data.Monoid                      (Monoid, mempty, mappend)
import           Data.Semigroup                   (Semigroup, (<>))
import           Control.Monad                    (ap)

data Collect err m = CFail err | CCollect m
  deriving (Functor)

type Collect_ = Collect ()

instance (Semigroup m) => Semigroup (Collect err m) where
  CFail e     <> _           = CFail e
  _           <> CFail e     = CFail e
  CCollect m1 <> CCollect m2 = CCollect $ m1 <> m2

instance (Monoid m) => Monoid (Collect err m) where
  mempty = CCollect mempty

  CFail e     `mappend` _           = CFail e
  _           `mappend` CFail e     = CFail e
  CCollect m1 `mappend` CCollect m2 = CCollect $ m1 `mappend` m2

instance Applicative (Collect err) where
  pure = return

  (<*>) = ap

instance Monad (Collect err) where
  return = CCollect

  CFail err  >>= _ = CFail err
  CCollect x >>= f = f x
