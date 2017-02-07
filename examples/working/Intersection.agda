module Intersection where

postulate A : Set
postulate C : Set
postulate c : (a : A) -> C

MA : (x : A) (y : A) -> C
MA = _

constr1 : (x : A) (y : A) (z : A) -> MA x z == MA y z
constr1 _ _ _ = refl

constr2 : (x : A) -> MA x x == c x
constr2 _ = refl
