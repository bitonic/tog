module CurryWhenPruning where

open import Prelude

data Bool : Set
data Bool where
  true  : Bool
  false : Bool

record Times (A B : Set) : Set
record Times A B where
  constructor pair
  field
    fst : A
    snd : B

open Times

postulate foo : Bool -> Bool

dummy : Bool

X : Bool -> Bool
X = _

Y : Times Bool Bool -> Bool
Y = _

solveY : {x : Bool} -> Y (pair x x) == x
solveY = refl

test : {x y : Bool} -> X x == foo (Y (pair x y))
test = refl

dummy = false
