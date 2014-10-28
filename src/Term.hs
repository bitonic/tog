module Term
  ( module Term.Types
  , module Term.Synonyms
  , module Term.Pretty
  , module Term.FreeVars
  , module Term.Nf
  , module Term.MetaVars
  , module Term.Substitution.Utils
  , Ctx
  , Tel
  , Substitution
  ) where

import Term.Types
import Term.Synonyms
import Term.Pretty
import Term.FreeVars
import Term.Nf
import Term.MetaVars
import Term.Substitution.Utils
import Term.Context (Ctx)
import Term.Telescope (Tel)
import Term.Substitution (Substitution)

