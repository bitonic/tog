module Invariants where

-- open import Prelude

data Bool : Set
data Bool where
  true  : Bool
  false : Bool

not : Bool -> Bool
not true = false
not false = true

data Nat : Set
data Nat where
  zero : Nat
  suc : Nat -> Nat

record Unit : Set
record Unit where
  constructor tt

Foo : Bool -> Set
Foo true  = Nat
Foo false = Bool

-- The dummy stuff is to make sure that agda is able to instantiate the
-- meta

dummy : Unit

Y : Bool
Y = _

test : ((x : Foo Y) -> Foo (not x)) -> Nat
test g = g false

dummy = tt
