module Term.Subst where

import           Bound                            (Scope(Scope), Var(B, F))
import           Bound.Scope                      (unscope)
import qualified Bound.Scope.Simple               as Bound.Simple
import           Control.Comonad                  (Comonad, extract)
import           Data.Void                        (Void, absurd)

-- | Substitution of variables.  We don't use monad because the monad
-- laws will not be respected for some instances: for example `subst'
-- might be strict on the first argument.
class Subst t where
  var :: a -> t a
  subst :: t a -> (a -> t b) -> t b

  substMap :: (Subst t) => (a -> b) -> t a -> t b
  substMap f t = subst t (var . f)

substFromScope :: (Subst f) => Scope b f a -> f (Var b a)
substFromScope (Scope s) = subst s $ \v -> case v of
  F e -> substMap F e
  B b -> var (B b)

substToScope :: (Subst f) => f (Var b a) -> Scope b f a
substToScope e = Scope (substMap (fmap var) e)

substInstantiateName
  :: (Subst f, Comonad n) => (b -> f a) -> Scope (n b) f a -> f a
substInstantiateName k e = subst (unscope e) $ \v -> case v of
  B b -> k (extract b)
  F a -> a

substVacuous :: (Subst t) => t Void -> t a
substVacuous = substMap absurd

class Subst' t where
  subst' :: (Subst f) => t f a -> (a -> f b) -> t f b

instance Subst' (Scope b) where
  subst' (Scope s) f = Scope $ substMap (fmap (`subst` f)) s

instance Subst' (Bound.Simple.Scope b) where
  subst' (Bound.Simple.Scope s) f = Bound.Simple.Scope $ subst s $ \v -> case v of
    B v' -> var $ B v'
    F v' -> substMap F $ f v'

subst'Map :: (Subst' t, Subst f) => (a -> b) -> t f a -> t f b
subst'Map f t = subst' t (var . f)

subst'Vacuous :: (Subst f, Subst' t) => t f Void -> t f a
subst'Vacuous = subst'Map absurd
