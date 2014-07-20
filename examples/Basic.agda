
module Basic where

open import Prelude

data List (A : Set) : Set

data List A where
  nil  : List A
  cons : A -> List A -> List A

append : {A : Set} -> List A -> List A -> List A
append nil ys = ys
append (cons x xs) ys = cons x (append xs ys)

record Equiv {A : Set} (R : A -> A -> Set) : Set
record Equiv {A} R where
  constructor equiv
  field
    ref : (x : A) -> R x x
    sym : (x : A) (y : A) -> R x y -> R y x
    trans : (x y z : A) -> R x y -> R y z -> R x z

open Equiv

trans1 : {A : Set}{R : A -> A -> Set}{x y z : A} -> Equiv R -> R x y -> R y z -> R x z
trans1 eq p q = trans eq _ _ _ p q

postulate
  symId   : {A : Set} (x y : A) -> x == y -> y == x
  transId : {A : Set} {x y z : A} -> x == y -> y == z -> x == z

equivId : {A : Set} -> Equiv {A} (\x y -> x == y)
equivId {A} = equiv (\x -> refl) symId (\ x y z -> transId)

record Sigma (A : Set) (B : A -> Set) : Set
record Sigma A B where
  constructor pair
  field fst : A
        snd : B fst

record True : Set
record True where
  constructor tt

