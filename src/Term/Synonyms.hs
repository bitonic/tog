module Term.Synonyms where

import           Term.Nat

-- Useful type synonyms
------------------------------------------------------------------------

type Type (t :: Nat -> *) = t
type Term (t :: Nat -> *) = t

type Closed (t :: Nat -> *) = t Zero
