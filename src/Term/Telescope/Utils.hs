module Term.Telescope.Utils where

import           Prelude                          hiding (pi, length, lookup, (++))

import           Control.Applicative              ((<$>), (<*>), pure)
import           Control.Monad                    (liftM)
import           Data.Foldable                    (Foldable(foldMap))
import           Data.Monoid                      (mempty, (<>))
import           Data.Traversable                 (Traversable, sequenceA)
import           Data.Typeable                    (Typeable)
import           Data.Void                        (Void)

import           Syntax.Internal                  (Name)
import           Term.Class
import qualified Term.Context                     as Ctx
import           Term.Nat
import           Term.Subst
import           Term.Telescope                   hiding (instantiate)
import           Term.TermM
import           Term.Var

instance Subst' Proxy where
     subst' Proxy _ = return Proxy

instance Subst' Id where
  subst' (Id t) f = Id <$> subst t f

instance Subst' Prod2 where
  subst' (Prod2 x y) f = Prod2 <$> subst x f <*> subst y f

instance (Subst' t) => Subst' (Tel t) where
    subst' (Empty t)              f = Empty <$> subst' t f
    subst' (Cons (n, type_) tel') f = Cons <$> ((n, ) <$> subst type_ f) <*> subst' tel' f'
      where
        -- TODO replace the substMap here with a weaken
        f' (B n') = var $ B n'
        f' (F v)  = weaken =<< f v

-- | Instantiates an 'IdTel' repeatedly until we get to the bottom of
-- it.  Fails If the length of the 'Tel' and the provided list don't
-- match.
substs :: (IsTerm f) => IdTel f v0 -> [f v0] -> TermM (f v0)
substs (Empty t)     []           = return $ unId t
substs (Empty _)     (_ : _)      = error "Types.Telescope.instantiate: too many arguments"
substs (Cons _ _)    []           = error "Types.Telescope.instantiate: too few arguments"
substs (Cons _ tel') (arg : args) = (`substs` args) =<< subst' tel' instArg
  where
    instArg (B _) = return arg
    instArg (F v) = var v

-- | Instantiates a bound variable.
instantiate :: (IsTerm f, Subst' t) => Tel t f (Suc v) -> f v -> TermM (Tel t f v)
instantiate tel' t = subst' tel' inst
  where
    inst (B _) = return t
    inst (F v) = var v
