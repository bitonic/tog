{-# OPTIONS --type-in-type --without-K #-}
module HierReduced where

-- open import Prelude

subst : {A : Set} {x y : A} (P : A -> Set) ->
        x == y -> P x -> P y
subst P = J (\ x y _ -> P x -> P y) (\ x p -> p)

sym : {A : Set} {x y : A} -> x == y -> y == x
sym {A} {x} p = subst (\ y -> y == x) p refl

---

Pi : (S : Set)(T : S -> Set) -> Set
Pi S T = (s : S) -> T s

record Sg (S : Set)(T : S -> Set) : Set where
  constructor pair
  field
    fst : S
    snd : T fst
-- open Sg public

data Wi (I : Set)(S : I -> Set)(P : (i : I) -> S i -> Set)
        (r : (i : I)(s : S i) -> P i s -> I)(i : I) : Set where
  wi : (s : S i) (f : (p : P i s) -> Wi I S P r (r i s p)) -> Wi I S P r i

data Zero : Set where {}
kill : {X : Set} -> Zero -> X
kill ()
Kill : {X : Set} -> Zero -> X
Kill ()

record One : Set where constructor tt
data Two : Set where
  true : Two
  false : Two

True : Two -> Set
True true = One
True false = Zero

twoEq : Two -> Two -> Two
twoEq true true = true
twoEq false false = true
twoEq _ _ = false

bsubst : (b c : Two) -> True (twoEq b c) -> True b -> True c
bsubst true true _ x = x
bsubst false false _ x = x
bsubst true false () x
bsubst false true () x

data Ki : Set where
  set : Ki
  prop : Ki

isSet : Ki -> Set
isSet set = One
isSet prop = Zero

record LEVEL : Set where
  constructor level
  field
    uni  : Ki -> Set
    el   : (k : Ki) -> uni k -> Set
-- open LEVEL public

data UpU (L : LEVEL)(k : Ki) : Set
UpEl : {L : LEVEL}{k : Ki} -> UpU L k -> Set

data UpU L k where
  U' : {q : isSet k} -> Ki -> UpU L k
  El' : (T : uni L k) -> UpU L k
  Prf' : {q : isSet k}(P : UpU L prop) -> UpU L k
  B' : Two -> UpU L k
  Two' : {q : isSet k} -> UpU L k
  Pi' : (S : UpU L set)(T : UpEl S -> UpU L k) -> UpU L k
  Sg' : (S : UpU L k)(T : UpEl S -> UpU L k) -> UpU L k
  Wi' : (I : UpU L set)
        (S : UpEl I ->  UpU L k)
        (P : (i : UpEl I)(s : UpEl (S i)) -> UpU L set)
        (r : (i : UpEl I)(s : UpEl (S i))(p : UpEl (P i s)) -> UpEl I)
        (i : UpEl I) -> UpU L k

UpEl {L} (U' k) = uni L k
UpEl {L} (El' T) = el L _ T
UpEl (Prf' P) = UpEl P
UpEl (B' b) = True b
UpEl Two' = Two
UpEl (Pi' S T) = Pi (UpEl S) (\ s -> UpEl (T s))
UpEl (Sg' S T) = Sg (UpEl S) (\ s -> UpEl (T s))
UpEl (Wi' I S P r i) =
  Wi (UpEl I) (\ i -> UpEl (S i)) (\ i s -> UpEl (P i s)) r i

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

Level : Nat -> LEVEL
Level ze = level (\ _ -> Zero) (\_ -> Kill)
Level (su n) = level (UpU (Level n)) (\_ -> UpEl {Level n})

raise : Ki -> Nat -> Set
raise k n = UpU (Level n) k

EL : (n : Nat) -> raise set n -> Set
EL n T = UpEl {Level n} T
PRF : (n : Nat) -> raise prop n -> raise set n
PRF n P = Prf' P

natEq : (n : Nat) -> Nat -> Nat -> raise prop n
natEq _ ze ze = (B' true)
natEq p (su m) (su n) = natEq p m n
natEq _ _ _ = (B' false)

nsubst : (p m n : Nat) -> EL p (PRF p (natEq p m n)) ->
         (P : Nat -> Set) -> P m -> P n
nsubst p ze ze _ P x = x
nsubst p ze (su n) () _ _
nsubst p (su m) ze () _ _
nsubst p (su m) (su n) q P x = nsubst p m n q (\ i -> P (su i)) x

record Embedding (m n : Nat) : Set where
  constructor embed
  field
    Em  : (k : Ki) -> raise k m ->  raise k n
    Nop : (k : Ki)(T : raise k m) -> UpEl {Level n} (Em k T) ==  UpEl {Level m} T
-- open Embedding public

idEm : {n : Nat} -> Embedding n n
idEm = embed (\ k T -> T) (\ k T -> refl)

suEm : {m n : Nat} -> Embedding (su m) n -> Embedding m n
suEm emb = embed (\ k T -> Em emb k (El' T)) (\ k T -> Nop emb k (El' T))

COE : {S T : Set} -> S == T -> S -> T
COE p s = subst (\ A -> A) p s

EOC : {S T : Set} -> S == T -> T -> S
EOC p s = subst (\ A -> A) (sym p) s

Times' : {k : Ki}(n : Nat) -> raise k n -> raise k n -> raise k n
Times' _ P Q = Sg' P (\ _ -> Q)

Fun' : (n : Nat) -> raise prop n -> raise prop n -> raise prop n
Fun' _ P Q = Pi' (Prf' P) (\ _ -> Q)

upPi' : {k : Ki}{n p : Nat}(E : Embedding n p) ->
        (S : raise set n) -> (EL n S -> raise k p) -> raise k p
upPi' E S T = Pi' (Em E set S) (\ s' -> T (COE (Nop E set S) s'))


PROPEQ : (m : Nat)(P : raise prop m)(n : Nat)(Q : raise prop n) ->
        (p : Nat)(mp : Embedding m p)(np : Embedding n p) ->
        raise prop p
SETEQ : (m : Nat)(S : raise set m)(n : Nat)(T : raise set n) ->
        (p : Nat)(mp : Embedding m p)(np : Embedding n p) ->
        raise prop p
VALEQ : (m : Nat)(S : raise set m)(s : EL m S)
        (n : Nat)(T : raise set n)(t : EL n T) ->
        (p : Nat)(mp : Embedding m p)(np : Embedding n p) ->
        raise prop p

PROPEQ m P n Q p mp np =
  Times' p (Fun' p (Em mp prop P) (Em np prop Q))
           (Fun' p (Em np prop Q) (Em mp prop P))

SETEQ m (U' _) n (Prf' _) _ _ _ = (B' false)
SETEQ m (U' _) n (B' _) _ _ _ = (B' false)
SETEQ m (U' _) n Two' _ _ _ = (B' false)
SETEQ m (U' _) n (Pi' _ _) _ _ _ = (B' false)
SETEQ m (U' _) n (Sg' _ _) _ _ _ = (B' false)
SETEQ m (U' _) n (Wi' _ _ _ _ _) _ _ _ = (B' false)
SETEQ m (U' set) n (U' set) p mp np = natEq p m n
SETEQ m (U' prop) n (U' prop) p mp np = natEq p m n
SETEQ m (U' _) n (U' _) _ _ _ = (B' false)
SETEQ m (Prf' P) n (Prf' Q) p mp np = PROPEQ m P n Q p mp np
SETEQ m (Prf' P) n (U' _) _ _ _ = B' false
SETEQ m (Prf' P) n (B' _) _ _ _ = B' false
SETEQ m (Prf' P) n Two' _ _ _ = B' false
SETEQ m (Prf' P) n (Pi' _ _) _ _ _ = B' false
SETEQ m (Prf' P) n (Sg' _ _) _ _ _ = B' false
SETEQ m (Prf' P) n (Wi' _ _ _ _ _) _ _ _ = B' false
SETEQ m (B' b) n (B' c) p mp np = B' (twoEq b c)
SETEQ m (B' b) n (U' _) _ _ _ = B' false
SETEQ m (B' b) n (Prf' _) _ _ _ = B' false
SETEQ m (B' b) n Two' _ _ _ = B' false
SETEQ m (B' b) n (Pi' _ _) _ _ _ = B' false
SETEQ m (B' b) n (Sg' _ _) _ _ _ = B' false
SETEQ m (B' b) n (Wi' _ _ _ _ _) _ _ _ = B' false
SETEQ m Two' n Two' p mp np = (B' true)
SETEQ m Two' n (U' _) _ _ _ = B' false
SETEQ m Two' n (Prf' _) _ _ _ = B' false
SETEQ m Two' n (B' b) _ _ _ = B' false
SETEQ m Two' n (Pi' _ _) _ _ _ = B' false
SETEQ m Two' n (Sg' _ _) _ _ _ = B' false
SETEQ m Two' n (Wi' _ _ _ _ _) _ _ _ = B' false
SETEQ m (Pi' S S') n (Pi' T T') p mp np =
  Times' p (SETEQ n T m S p np mp)
   (upPi' np T (\ t -> upPi' mp S (\ s ->
    Fun' p (VALEQ n T t m S s p np mp)
           (SETEQ m (S' s) n (T' t) p mp np))))
SETEQ m (Pi' S S') n (U' _) _ _ _ = B' false
SETEQ m (Pi' S S') n (Prf' _) _ _ _ = B' false
SETEQ m (Pi' S S') n (B' b) _ _ _ = B' false
SETEQ m (Pi' S S') n (Sg' _ _) _ _ _ = B' false
SETEQ m (Pi' S S') n Two' _ _ _ = B' false
SETEQ m (Pi' S S') n (Wi' _ _ _ _ _) _ _ _ = B' false
SETEQ m (Sg' S S') n (Sg' T T') p mp np =
  Times' p (SETEQ m S n T p mp np)
   (upPi' mp S (\ s -> upPi' np T (\ t ->
    Fun' p (VALEQ m S s n T t p mp np)
     (SETEQ m (S' s) n (T' t) p mp np))))
SETEQ m (Sg' S S') n (U' _) _ _ _ = B' false
SETEQ m (Sg' S S') n (Prf' _) _ _ _ = B' false
SETEQ m (Sg' S S') n (B' b) _ _ _ = B' false
SETEQ m (Sg' S S') n (Pi' _ _) _ _ _ = B' false
SETEQ m (Sg' S S') n Two' _ _ _ = B' false
SETEQ m (Sg' S S') n (Wi' _ _ _ _ _) _ _ _ = B' false
SETEQ m (Wi' I S P r i) n (Wi' J_ T Q u j) p mp np =
  Times' p (SETEQ m I n J_ p mp np)
   (Times' p (VALEQ m I i n J_ j p mp np)
     (upPi' mp I (\ i -> upPi' np J_ (\ j ->
      Fun' p (VALEQ m I i n J_ j p mp np)
       (Times' p (SETEQ m (S i) n (T j) p mp np)
         (upPi' mp (S i) (\ s -> upPi' np (T j) (\ t ->
           Fun' p (VALEQ m (S i) s n (T j) t p mp np)
            (Times' p (SETEQ n (Q j t) m (P i s) p np mp)
              (upPi' np (Q j t) (\ q -> upPi' mp (P i s) (\ o ->
                Fun' p (VALEQ n (Q j t) q m (P i s) o p np mp)
                 (VALEQ m I (r i s o) n J_ (u j t q) p mp np)))))))))))))
SETEQ m (Wi' _ _ _ _ _) n (U' _) _ _ _ = B' false
SETEQ m (Wi' _ _ _ _ _) n (Prf' _) _ _ _ = B' false
SETEQ m (Wi' _ _ _ _ _) n (B' b) _ _ _ = B' false
SETEQ m (Wi' _ _ _ _ _) n (Pi' _ _) _ _ _ = B' false
SETEQ m (Wi' _ _ _ _ _) n Two' _ _ _ = B' false
SETEQ m (Wi' _ _ _ _ _) n (Sg' _ _) _ _ _ = B' false
SETEQ ze (El' ()) n T p mp np
SETEQ (su m) (El' S) n T p mp np = SETEQ m S n T p (suEm mp) np
SETEQ m S ze (El' ()) p mp np
SETEQ m S (su n) (El' T) p mp np = SETEQ m S n T p mp (suEm np)

VALEQ m Two' true n Two' false p mp np = B' false
VALEQ m Two' false n Two' true p mp np = B' false
VALEQ m (Pi' S S') f n (Pi' T T') g p mp np =
  upPi' mp S (\ s -> upPi' np T (\ t ->
   Fun' p (VALEQ m S s n T t p mp np)
    (VALEQ m (S' s) (f s) n (T' t) (g t) p mp np)))
VALEQ m (Sg' S S') s n (Sg' T T') t p mp np =
  Times' p (VALEQ m S (fst s) n T (fst t) p mp np)
   (VALEQ m (S' (fst s)) (snd s) n (T' (fst t)) (snd t) p mp np)
VALEQ m (Wi' I S P r i) s n (Wi' J_ T Q u j) t p mp np =
  WEQ i s j t where
  WEQ : (i : EL m I)(s : EL m (Wi' I S P r i))
        (j : EL n J_)(t : EL n (Wi' J_ T Q u j)) -> raise prop p
  WEQ i (wi s f) j (wi t g) =
    Times' p (VALEQ m (S i) s n (T j) t p mp np)
     (upPi' mp (P i s) (\ p -> upPi' np (Q j t) (\ q -> 
       WEQ (r i s p) (f p) (u j t q) (g q))))
VALEQ ze (U' _) () n (U' _) t p mp np
VALEQ (su y) (U' _) s ze (U' _) () p mp np
VALEQ (su m) (U' set) S (su n) (U' set) T p mp np =
  SETEQ m S n T p (suEm mp) (suEm np)
VALEQ (su m) (U' prop) P (su n) (U' prop) Q p mp np =
  PROPEQ m P n Q p (suEm mp) (suEm np)
VALEQ ze (El' ()) s n T t p mp np
VALEQ (su m) (El' S) s n T t p mp np =
  VALEQ m S s n T t p (suEm mp) np
VALEQ m S s ze (El' ()) t p mp np
VALEQ m S s (su n) (El' T) t p mp np =
  VALEQ m S s n T t p mp (suEm np)
VALEQ m _ s n _ t p mp np = B' true

postulate axiom : (p : Nat)(P : raise prop p) -> EL p (Prf' P)
