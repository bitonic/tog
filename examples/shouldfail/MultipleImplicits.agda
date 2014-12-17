module MultipleImplicits where

-- These should fail since they contain 2 consecutive implicits.
const : {A : Set} -> {B : Set} -> A -> B -> A
const a b = a 

g : {A : Set} -> {B : A -> Set} -> (a : A) -> B a -> B a
g a B = B
