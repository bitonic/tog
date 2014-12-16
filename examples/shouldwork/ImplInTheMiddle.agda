module ImplInTheMiddle where

-- This should always work
const : {A : Set} -> {B : Set} -> A -> B -> A
const a b = a 

-- This should always work
g : {A : Set} -> {B : A -> Set} -> (a : A) -> B a -> B a
g a B = B

-- This should only work after the new handling of implicits.
f : {A : Set} -> A -> {B : Set} -> B -> A
f a b = a
