{-# LANGUAGE UndecidableInstances #-}
module Term.Subst where

import           Term.TermM
import           Term.Var
import           Term.Nat

-- | Substitution of variables.  We don't use monad because the monad
-- laws will not be respected for some instances: for example `subst'
-- might be strict on the first argument.
class Subst t where
  var :: Var a -> TermM (t a)
  subst :: t a -> (Var a -> TermM (t b)) -> TermM (t b)

  substMap :: (Var a -> Var b) -> t a -> TermM (t b)
  substMap f t = subst t (var . f)
