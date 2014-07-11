module Term.MetaVar where

import           Prelude.Extended
import qualified Text.PrettyPrint.Extended        as PP

-- 'MetaVar'iables
------------------------------------------------------------------------

-- | 'MetaVar'iables.  Globally scoped.
newtype MetaVar = MetaVar {unMetaVar :: Int}
    deriving (Eq, Ord, Hashable)

instance PP.Pretty MetaVar where
    prettyPrec _ = PP.text . show

instance Show MetaVar where
   show (MetaVar mv) = "_" ++ show mv
