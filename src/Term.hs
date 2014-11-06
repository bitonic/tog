-- | Terms and a lot of facilities.
--
-- 'Tel', 'Ctx', and 'Substitution' operations should be imported in a
-- qualified fashion:
--
-- @
-- import qualified Term.Context                     as Ctx
-- import qualified Term.Substitution                as Sub
-- import qualified Term.Telescope                   as Tel
-- @
module Term
  ( module Term.Types
  , module Term.Synonyms
  , module Term.FreeVars
  , module Term.Substitution.Utils
  , Ctx
  , Tel
  , Substitution
  ) where

-- We want to use the smart constructors only, and we should only use
-- whnfView.
import Term.Types hiding (unview, view)
import Term.Synonyms
import Term.Pretty ()
import Term.MetaVars ()
import Term.FreeVars
import Term.Substitution.Utils
import Term.Context (Ctx)
import Term.Telescope (Tel)
import Term.Substitution (Substitution)
