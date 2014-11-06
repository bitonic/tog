{-# OPTIONS --type-in-type #-}
module StuckDomains where

open import Prelude

data Bool : Set
data Bool where
  true : Bool
  false : Bool

record Unit : Set
record Unit where
  constructor tt

F : Bool -> Set
F true  = Bool
F false = Unit

X : Bool
Y : Bool
test1 : ((x : F X -> Set) -> (y : F X) -> x y) == ((x : F Y -> Set) -> (y : F Y) -> x y)
test2 : X == true
test3 : Y == true

X = _
Y = _
test1 = refl
test2 = refl
test3 = refl

