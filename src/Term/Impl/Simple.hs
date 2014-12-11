module Term.Impl.Simple (Simple) where

import           TogPrelude
import           Term.Types
import           Term.Impl.Common
import           System.IO.Unsafe                 (unsafePerformIO)

-- Base terms
------------------------------------------------------------------------

newtype Simple = S {unS :: TermView Simple}
    deriving (Eq, Show, Typeable)

instance Metas Simple Simple where
  metas = genericMetas

instance Nf Simple Simple where
  nf = genericNf

instance PrettyM Simple Simple where
  prettyPrecM = genericPrettyPrecM

instance ApplySubst Simple Simple where
  safeApplySubst = genericSafeApplySubst

instance SynEq Simple Simple where
  synEq x y = return (x == y)

instance IsTerm Simple where
  whnf = genericWhnf

  view = return . unS
  unview = return . S

  set = S Set
  refl = S Refl

  {-# NOINLINE typeOfJ #-}
  typeOfJ = unsafePerformIO $ runTermM sigEmpty genericTypeOfJ

