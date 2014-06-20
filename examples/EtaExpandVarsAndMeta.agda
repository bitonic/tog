module EtaExpandVarsAndMeta where

open import Prelude

record Pair (A : Set) (B : Set) : Set
record Pair A B where
  constructor pair
  field
    fst : A
    snd : B

open Pair

data Unit : Set
data Unit where
  tt : Unit

X : Unit -> Pair Unit Unit
X x = _

test : (x : Pair Unit Unit) -> X (fst x) == pair (fst x) (fst x)
test x = refl
