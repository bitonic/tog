module Term.Impl.Simple (Simple) where

import           Data.Typeable                    (Typeable)

import           Term
import qualified Term.Signature                   as Sig
import           Term.Impl.Common
import           System.IO.Unsafe                 (unsafePerformIO)

-- Base terms
------------------------------------------------------------------------

newtype Simple = S {unS :: TermView Simple}
    deriving (Eq, Show, Typeable)

instance MetaVars Simple Simple where
  metaVars = genericMetaVars

instance Nf Simple Simple where
  nf = genericNf

instance PrettyM Simple Simple where
  prettyPrecM = genericPrettyPrecM

instance Subst Simple Simple where
  applySubst = genericApplySubst

instance SynEq Simple Simple where
  synEq x y = return (x == y)

instance IsTerm Simple where
  whnf = genericWhnf

  view = return . unS
  unview = return . S

  set = S Set
  refl = S Refl
  typeOfJ = typeOfJS

{-# NOINLINE typeOfJS #-}
typeOfJS :: Closed Simple
typeOfJS = unsafePerformIO $ runTermM Sig.empty genericTypeOfJ

