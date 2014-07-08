module Term.Context
    ( -- * 'Ctx'
      Ctx(..)
    , ClosedCtx
    , singleton
    , length
    , (++)
    , weakenVar
    ) where

import           Prelude                          hiding (pi, length, lookup, (++))

import           Data.Typeable                    (Typeable)

import           Syntax.Internal                  (Name)
import           Term.Var
import           Term.Nat

-- Ctx
------------------------------------------------------------------------

-- | A 'Ctx' is a backwards list of named terms, each scoped over all
-- the previous ones.
data Ctx (v0 :: Nat) t (v :: Nat) where
    Empty :: Ctx v0 t v0
    Snoc  :: Ctx v0 t v -> (Name, t v) -> Ctx v0 t (Suc v)
    deriving (Typeable)

type ClosedCtx = Ctx Zero

singleton :: Name -> t v0 -> Ctx v0 t (Suc v0)
singleton name t = Snoc Empty (name, t)

length :: Ctx v0 t v -> Int
length Empty        = 0
length (Snoc ctx _) = 1 + length ctx

(++) :: Ctx v0 t v1 -> Ctx v1 t v2 -> Ctx v0 t v2
ctx1 ++ Empty                 = ctx1
ctx1 ++ (Snoc ctx2 namedType) = Snoc (ctx1 ++ ctx2) namedType

-- | Takes a variable outside the 'Ctx' and brings it inside.
weakenVar :: Ctx v0 t v -> Var v0 -> Var v
weakenVar Empty        v = v
weakenVar (Snoc ctx _) v = F (weakenVar ctx v)
