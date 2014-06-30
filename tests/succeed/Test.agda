module Test where

postulate
  A : Set
  B : Set

foo : (x : A) (y : B) -> Set
foo x = \_ -> B
