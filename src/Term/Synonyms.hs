module Term.Synonyms where

import           Data.Void                        (Void)

-- Useful type synonyms
------------------------------------------------------------------------

type Type (t :: * -> *) = t
type Term (t :: * -> *) = t

type Closed t = t Void
