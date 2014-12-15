module EmptyPattern where

data Bool : Set where
  true : Bool
  false : Bool

absurd : Bool -> (A : Set) -> A
absurd () _
