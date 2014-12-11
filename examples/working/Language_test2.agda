------------------------------------------------------------------------
-- A small definition of a dependently typed language, using the
-- technique from McBride's "Outrageous but Meaningful Coincidences"
------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

-- The code contains an example, a partial definition of categories,
-- which triggers the use of an enormous amount of memory (with the
-- development version of Agda which is current at the time of
-- writing). I'm not entirely sure if the code is correct: 2.5G heap
-- doesn't seem to suffice to typecheck this code. /NAD

module Language_test2 where

------------------------------------------------------------------------
-- Prelude

-- open import Prelude

subst : {A : Set} {x y : A} (P : A -> Set) ->
        x == y -> P x -> P y
subst P = J (\ x y _ -> P x -> P y) (\ x p -> p)

record Unit : Set
record Unit where
  constructor tt

-- open Unit

record Sigma (A : Set) (B : A -> Set) : Set
record Sigma A B where
  constructor pair
  field
    fst : A
    snd : B fst

-- open Sigma

------------------------------------------------------------------------
-- A universe

data U : Set

El : U -> Set

data U where
  set : U
  el  : Set -> U

El set = Set
El (el A) = A

------------------------------------------------------------------------
-- A language

-- Syntax for types.

Eq : (A : Set) -> A -> A -> Set
Eq _ x y = x == y

withType : (A : Set) -> A -> A
withType _ x = x

Alpha : U
raw-category : Sigma (Eq (Set -> U) (\ _ -> set) (\ _ -> set))
                     (\eq -> (\ g -> el (subst (\ f -> El (f g)) eq g)) == (\g -> el g))

Alpha = _
raw-category = pair (withType (Eq (El Alpha -> U) (\_ -> Alpha) (\_ -> Alpha)) refl) refl
