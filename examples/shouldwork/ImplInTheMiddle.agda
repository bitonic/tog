module ImplInTheMiddle where

-- This should only work after the new handling of implicits.
f : {A : Set} -> A -> {B : Set} -> B -> A
f a b = a
