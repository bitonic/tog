module Term.Subst where

import           Data.Void                        (Void)
import           Unsafe.Coerce                    (unsafeCoerce)

import           Term.TermM

-- | Substitution of variables.  We don't use monad because the monad
-- laws will not be respected for some instances: for example `subst'
-- might be strict on the first argument.
class Subst t where
  var :: a -> TermM (t a)
  subst :: t a -> (a -> TermM (t b)) -> TermM (t b)

  substMap :: (Subst t) => (a -> b) -> t a -> TermM (t b)
  substMap f t = subst t (var . f)

class Subst' t where
  subst' :: (Subst f) => t f a -> (a -> TermM (f b)) -> TermM (t f b)

subst'Map :: (Subst' t, Subst f) => (a -> b) -> t f a -> TermM (t f b)
subst'Map f t = subst' t (var . f)

-- TODO these are obviously very unsafe, I should have something better,
-- but I don't want them to live them in IO...

substVacuous :: (Subst t) => t Void -> t a
substVacuous = unsafeCoerce

subst'Vacuous :: (Subst' t, Subst f) => t f Void -> t f a
subst'Vacuous = unsafeCoerce