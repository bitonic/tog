{-# OPTIONS --type-in-type #-}
module Prelude where

data _==_ {A : Set}(x : A) : A → Set where
  refl : x == x

J : {A : Set} {x y : A} (P : (x y : A) → x == y -> Set) →
    (∀ z → P z z refl) → (p : x == y) → P x y p
J P h refl = h _

-- J : {A B : Set} (P : (A B : Set) → A == B -> Set) →
--     (∀ C → P C C refl) → (p : A == B) → P A B p

subst : {A : Set} {x y : A} (P : A -> Set) ->
        x == y -> P x -> P y
subst P = J (\ x y _ -> P x -> P y) (\ x p -> p)

coe : {A B : Set} -> A == B -> (x : A) -> B
coe p x = J (\ A B _ → A → B) (λ _ A → A) p x
