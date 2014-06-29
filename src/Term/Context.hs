module Term.Context
    ( -- * 'Ctx'
      Ctx(..)
    , ClosedCtx
    , singleton
    , length
    , elemIndex
    , (++)
    , weakenVar
    ) where

import           Prelude                          hiding (pi, length, lookup, (++))

import           Bound
import           Data.Typeable                    (Typeable)
import           Data.Void                        (Void, absurd)

import           Syntax.Internal                  (Name)
import           Term.Var

-- Ctx
------------------------------------------------------------------------

-- | A 'Ctx' is a backwards list of named terms, each scoped over all
-- the previous ones.
data Ctx v0 t v where
    Empty :: Ctx v0 t v0
    Snoc  :: (IsVar v) => Ctx v0 t v -> (Name, t v) -> Ctx v0 t (TermVar v)
    deriving (Typeable)

type ClosedCtx = Ctx Void

singleton :: (IsVar v0) => Name -> t v0 -> Ctx v0 t (TermVar v0)
singleton name t = Snoc Empty (name, t)

length :: Ctx v0 t v -> Int
length Empty        = 0
length (Snoc ctx _) = 1 + length ctx

-- | Gets the index of a variable *from the right*.  0-indexed.  So the
-- rightmost type will have index @0@, and the leftmost type will have
-- index @length 'Ctx' - 1@.  Also returns the name at that index.
elemIndex :: v -> ClosedCtx t v -> Named Int
elemIndex v0 ctx0 = go ctx0 v0
  where
    go :: ClosedCtx t v -> v -> Named Int
    go Empty v = absurd v
    go (Snoc _ctx (n, _type)) (B _) = named n 0
    go (Snoc  ctx _         ) (F v) = fmap (+ 1) $ go ctx v

(++) :: Ctx v0 t v1 -> Ctx v1 t v2 -> Ctx v0 t v2
ctx1 ++ Empty                 = ctx1
ctx1 ++ (Snoc ctx2 namedType) = Snoc (ctx1 ++ ctx2) namedType

-- | Takes a variable outside the 'Ctx' and brings it inside.
weakenVar :: Ctx v0 t v -> v0 -> v
weakenVar Empty        v = v
weakenVar (Snoc ctx _) v = F (weakenVar ctx v)
