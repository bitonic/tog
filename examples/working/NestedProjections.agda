module NestedProjections where

-- open import Prelude

record Times (A : Set) (B : Set) : Set
record Times A B where
  constructor pair
  field
    fst : A
    snd : B
-- open Times

data Bool : Set
data Bool where
  true : Bool
  false : Bool

dummy : Bool

X : Times Bool Bool -> Bool
X = _

test : (x y : Times Bool Bool) -> X (pair (fst x) (fst y)) == fst x
test _ _ = refl

dummy = true
