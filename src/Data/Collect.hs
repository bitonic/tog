module Data.Collect where

import           Data.Monoid                      (Monoid, mempty, mappend)
import           Data.Semigroup                   (Semigroup, (<>))

data Collect err m = CFail err | CCollect m

instance (Semigroup m) => Semigroup (Collect err m) where
  CFail e     <> _           = CFail e
  _           <> CFail e     = CFail e
  CCollect m1 <> CCollect m2 = CCollect $ m1 <> m2

instance (Monoid m) => Monoid (Collect err m) where
  mempty = CCollect mempty

  CFail e     `mappend` _           = CFail e
  _           `mappend` CFail e     = CFail e
  CCollect m1 `mappend` CCollect m2 = CCollect $ m1 `mappend` m2

type Collect_ = Collect ()
