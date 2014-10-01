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

instance IsTerm Simple where
  -- termEq = genericTermEq
  strengthen = genericStrengthen
  getAbsName' = genericGetAbsName

  whnf = genericWhnf
  nf = genericNf

  view = return . unS
  unview = return . S

  set = S Set
  refl = S Refl
  typeOfJ = typeOfJS

  substs = genericSubsts
  weaken = genericWeaken

{-# NOINLINE typeOfJS #-}
typeOfJS :: Closed Simple
typeOfJS = unsafePerformIO $ monadTermIO Sig.empty genericTypeOfJ

