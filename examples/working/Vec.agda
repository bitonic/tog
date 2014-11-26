module Vec where

-- -- Families

-- data Vec (A : Set) : Nat -> Set where
--   []   : Vec A zero
--   _::_ : {n : Nat} (x : A) (xs : Vec A n) -> Vec A (suc n)

-- Properties of equality.

subst : {A : Set} {x y : A} (P : A -> Set) ->
        x == y -> P x -> P y
subst P = J (\ x y _ -> P x -> P y) (\ x p -> p)

sym : {A : Set} {x : A} {y : A} -> x == y -> y == x
sym {A} {x} {y} p = subst (\ y -> y == x) p refl

trans : {A : Set} {x : A} {y : A} {z : A} -> x == y -> y == z -> x == z
trans {A} {x} p q = subst (\ y -> x == y) q p

cong : {A B : Set} {x : A} {y : A} (f : A -> B) -> x == y -> f x == f y
cong f p = subst (\ y -> f _ == f y) p refl

-- Just parametrized data types.

data Nat : Set

data Nat where
  zero : Nat
  suc  : (n : Nat) -> Nat

pred : Nat -> Nat
pred zero    = zero
pred (suc n) = n

-- Equality on natural numbers

data Unit : Set
data Unit where
  unit : Unit

Empty : Set
Empty = (A : Set) -> A

IsZero : Nat -> Set
IsZero zero    = Unit
IsZero (suc n) = Empty

zeroNOTsuc : {n : Nat} -> zero == suc n -> Empty
zeroNOTsuc p = subst IsZero p unit

sucInj : {n m : Nat} -> suc n == suc m -> n == m
sucInj p = cong pred p

lemma : {n m : Nat} -> n == suc m -> n == zero -> Empty
lemma p q = zeroNOTsuc (trans (sym q) p)

-- Vectors

data Vec (A : Set) (n : Nat) : Set
data Vec A n where
  nil  : n == zero -> Vec A n
  cons : {m : Nat} (p : n == suc m) (x : A) (xs : Vec A m) -> Vec A n

data Fin (n : Nat) : Set
data Fin n where
  fzero : {m : Nat} (p : n == suc m) -> Fin n
  fsuc  : {m : Nat} (p : n == suc m) (i : Fin m) -> Fin n

lookup : {A : Set} (n : Nat) (i : Fin n) (v : Vec A n) -> A
lookup {A} n (fzero {m} p) (nil q)            = lemma p q A
lookup {A} n (fzero {m} p) (cons {l} q x xs)  = x
lookup {A} n (fsuc {m} p i) (nil q)           = lemma p q A
lookup {A} n (fsuc {m} p i) (cons {l} q x xs) =
  lookup m i (subst (Vec A) (sucInj (trans (sym q) p)) xs)
