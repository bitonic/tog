module Term.Telescope.Types where

import           Prelude.Extended
import           Syntax
import           Term.Synonyms

-- | A 'Tel' is a list of types, each one ranging over the rest of the
-- list, and with something of at the end -- the inverse of a 'Ctx.Ctx',
-- plus the end element.
data Tel t
    = Empty
    | Cons (Name, t) (Tel (Abs t))
    deriving (Eq, Ord, Show, Typeable)
