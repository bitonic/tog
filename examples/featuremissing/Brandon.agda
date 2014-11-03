module Brandon where

data Nat : Set
data Nat where
  zero : Nat
  suc  : Nat -> Nat

data Times (A B : Set) : Set
data Times A B where
  times : A -> B -> Times A B

F : Nat -> Set
F zero = Nat
F (suc n) = Times Nat (F n)

f : (n : Nat) -> F n
f zero = zero
f (suc n) = times n (f n)

n : Nat
n = _

test : F n
test = f (suc n)
