{-# LANGUAGE UndecidableInstances #-}
module Term.Subst where

import           Data.Hashable                    (Hashable)
import           Data.Void                        (Void)
import           Unsafe.Coerce                    (unsafeCoerce)
import           Data.Typeable                    (Typeable)

import           Term.TermM

class (Typeable v, Eq v, Ord v, Hashable v) => SubstVar v

instance (Eq v, Ord v, Hashable v, Typeable v) => SubstVar v

-- | Substitution of variables.  We don't use monad because the monad
-- laws will not be respected for some instances: for example `subst'
-- might be strict on the first argument.
class Subst t where
  var :: SubstVar a => a -> TermM (t a)
  subst :: (SubstVar a, SubstVar b) => t a -> (a -> TermM (t b)) -> TermM (t b)

  substMap :: (SubstVar a, SubstVar b, Subst t) => (a -> b) -> t a -> TermM (t b)
  substMap f t = subst t (var . f)

class Subst' t where
  subst' :: (SubstVar a, SubstVar b, Subst f) => t f a -> (a -> TermM (f b)) -> TermM (t f b)

subst'Map :: (SubstVar a, SubstVar b, Subst' t, Subst f) => (a -> b) -> t f a -> TermM (t f b)
subst'Map f t = subst' t (var . f)

-- TODO these are obviously very unsafe, I should have something better,
-- but I don't want them to live them in IO...

substVacuous :: (Subst t) => t Void -> t a
substVacuous = unsafeCoerce

subst'Vacuous :: (Subst' t, Subst f) => t f Void -> t f a
subst'Vacuous = unsafeCoerce