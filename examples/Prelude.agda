{-# OPTIONS --type-in-type #-}
{-# OPTIONS --without-K #-}
module Prelude where

data _≅_ {A : Set}(x : A) : {B : Set} -> B → Set where
  refl : x ≅ x

J≅ : {A B : Set} {x : A} {y : B}
     (P : (x : A) (B : Set) (y : B) -> x ≅ y -> Set) →
     (∀ z → P z A z refl) → (p : x ≅ y) → P x B y p
J≅ P h refl = h _

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

J≡ : {A : Set} {x y : A}
     (P : (x : A) (y : A) -> x ≡ y -> Set) →
     (∀ z → P z z refl) → (p : x ≡ y) → P x y p
J≡ P h refl = h _

-- ≅-to-≡ : {A : Set} {x y : A} → x ≅ y → x ≡ y
-- ≅-to-≡ p = J≅ (\ x _ y _ -> x ≡ y) (\ _ -> refl) p

-- subst≡ : {A : Set} {x y : A} (P : A -> Set) ->
--          x ≡ y -> P x -> P y
-- subst≡ P = J≡ (\ x y _ -> P x -> P y) (\ x p -> p)

-- subst≅ : {A : Set} {x y : A} (P : A -> Set) ->
--          x ≅ y -> P x -> P y
-- subst≅ P p = subst≡ P (≅-to-≡ p)

-- subst₁ : {A : Set} {x y : A} (P : A -> Set) ->
--          x ≅ y -> P x -> P y
-- subst₁ P refl x = x

-- subst₂ : {A : Set} {x y : A} (P : A -> Set) ->
--          x ≅ y -> P x -> P y
-- subst₂ P p x = J {!!} {!!} p

-- coe : {A B : Set} -> A ≅ B -> (x : A) -> B
-- coe p x = subst₁ (\ A -> A) p x

-- coe : {A B : Set} -> A ≅ B -> (x : A) -> B
-- coe p x = J (\ A _ B → A → B) (λ _ A → A) p x
