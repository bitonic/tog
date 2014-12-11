module InvertFunction where

-- open import Prelude

data Bool : Set
data Bool where
  true  : Bool
  false : Bool

not : Bool -> Bool
not true = false
not false = true

X : Bool -> Bool
X = _

test1 : (x : Bool) -> X x == true
test1 x = refl

Y : Bool
Y = _

test2 : not Y == true
test2 = refl

