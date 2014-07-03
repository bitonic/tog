module Term.Var where

import           Bound                            (Var(B, F))
import qualified Bound.Name                       as Bound
import           Data.Hashable                    (Hashable)
import           Data.Typeable                    (Typeable)
import           Data.Void                        (Void, absurd)

import           Syntax.Internal                  (Name)
import           Term.Subst

-- Var
------------------------------------------------------------------------

-- | We use this type for bound variables of which we want to remember
-- the original name.
type Named = Bound.Name Name

named :: Name -> a -> Named a
named = Bound.Name

unNamed :: Named a -> a
unNamed (Bound.Name _ x) = x

-- 'IsVar' variables
------------------------------------------------------------------------

class VarName v where
    varName :: v -> Name

class VarIndex v where
    varIndex :: v -> Int

class (SubstVar v, Typeable v, VarName v, VarIndex v) => IsVar v

instance VarName Void where
    varName = absurd

instance VarIndex Void where
    varIndex = absurd

instance IsVar Void

instance (VarName v) => VarName (Var (Named a) v) where
    varName (B v) = Bound.name v
    varName (F v) = varName v

instance (VarIndex v) => VarIndex (Var (Named ()) v) where
    varIndex (B _) = 0
    varIndex (F v) = 1 + varIndex v

instance VarIndex (Var (Named Int) Void) where
    varIndex (B v) = unNamed v
    varIndex (F v) = absurd v

instance (IsVar v) => IsVar (Var (Named ()) v) where

instance IsVar (Var (Named Int) Void) where

instance VarName Name where
    varName = id

-- TermVar
------------------------------------------------------------------------

-- | A 'Var' with one 'Named' free variable.
type TermVar = Var (Named ())

boundTermVar :: Name -> TermVar v
boundTermVar n = B $ named n ()

-- Record 'Field's
------------------------------------------------------------------------

-- | The field of a projection.
newtype Field = Field {unField :: Int}
    deriving (Eq, Ord, Show, Hashable)
