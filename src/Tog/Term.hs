-- | Terms and a lot of facilities.  Output of typechecking.
module Tog.Term
  ( module Tog.Term.Types
    -- * Useful synonyms
  , module Tog.Term.Synonyms
    -- * Free variables
  , module Tog.Term.FreeVars
    -- * 'IsTerm' implementations
  , module Tog.Term.Impl
  ) where

-- We want to use the smart constructors only, and we should only use
-- whnfView.
import Tog.Term.Types hiding (unview, view)
import Tog.Term.Synonyms
import Tog.Term.Pretty ()
import Tog.Term.MetaVars ()
import Tog.Term.FreeVars
import Tog.Term.Impl
