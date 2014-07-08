module Term.Nat where

import           Data.Typeable                    (Typeable)

data Nat = Zero | Suc Nat

deriving instance Typeable Zero
deriving instance Typeable Suc
