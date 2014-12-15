module EmptyPattern where

data Empty : Set where {}

absurd : Empty -> (A : Set) -> A
absurd () _
