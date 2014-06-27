{-# OPTIONS --type-in-type #-}
module Ids2 where

open import Prelude

id : (A : Set) -> A -> A
id _ x = x

postulate A : Set

X1 : Set
X2 : Set
slow1 : A -> A
slow2 : A -> A

X1 = _
slow1 = id X1 (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _)

X2 = _
slow2 = id X2 (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _) (id _)

test : X1 == X2
test = refl

-- The example above is based on one in "Implementing Typed
-- Intermediate Languages" by Shao, League and Monnier.
