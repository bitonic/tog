module Term.Var where

import           Data.Foldable                    (Foldable)
import           Data.Hashable                    (Hashable, hashWithSalt)
import           Data.Traversable                 (Traversable)
import           Data.Typeable                    (Typeable)
import           Unsafe.Coerce                    (unsafeCoerce)

import           Syntax.Internal                  (Name)
import           Term.Nat

-- Var
------------------------------------------------------------------------

data Var (n :: Nat) where
  B :: Named () -> Var (Suc n)
  F :: Var n -> Var (Suc n)

deriving instance Eq (Var n)
deriving instance Ord (Var n)
deriving instance Typeable Var

varIndex :: Var n -> Int
varIndex (B _) = 0
varIndex (F n) = 1 + varIndex n

varName :: Var n -> Name
varName (B n) = namedName n
varName (F v) = varName v

instance Show (Var n) where
  show v = show (varIndex v) ++ "#" ++ show (varName v)

elimZeroVar :: Var Zero -> a
elimZeroVar = error "elimZeroVar"

instance Hashable (Var n) where
  hashWithSalt s = hashWithSalt s . varIndex

boundVar :: Name -> Var (Suc n)
boundVar n = B (named n ())

unvar :: (Named () -> a) -> (Var n -> a) -> Var (Suc n) -> a
unvar f _ (B n) = f n
unvar _ f (F v) = f v

-- Named
------------------------------------------------------------------------

named :: Name -> a -> Named a
named = Named

data Named a = Named
  { namedName :: Name
  , unNamed   :: a
  } deriving (Functor, Foldable, Traversable)

instance Eq a => Eq (Named a) where
  Named _ v1 == Named _ v2 = v1 == v2

instance Ord a => Ord (Named a) where
  Named _ v1 `compare` Named _ v2 = v1 `compare` v2

instance Hashable a => Hashable (Named a) where
  hashWithSalt s (Named _ v) = hashWithSalt s v

-- Record 'Field's
------------------------------------------------------------------------

-- | The field of a projection.
newtype Field = Field {unField :: Int}
    deriving (Eq, Ord, Show, Hashable)
