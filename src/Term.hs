-- | Terms and a lot of facilities.
module Term
  ( module Term.Types
  , module Term.Synonyms
  , module Term.FreeVars
  , module Term.Impl
  ) where

-- We want to use the smart constructors only, and we should only use
-- whnfView.
import Term.Types hiding (unview, view)
import Term.Synonyms
import Term.Pretty ()
import Term.MetaVars ()
import Term.FreeVars
import Term.Impl
