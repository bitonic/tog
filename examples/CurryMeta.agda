module CurryMeta where

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

X : Pair Unit Unit -> Unit
X x = _

foo : (x y : Unit) -> X (pair x y) == x
foo x y = refl
