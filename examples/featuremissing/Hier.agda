{-# OPTIONS --type-in-type --without-K #-}
module Hier where

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

coe : (m : Nat)(S : raise set m)(n : Nat)(T : raise set n) ->
      (p : Nat)(mp : Embedding m p)(np : Embedding n p) ->
      EL p (Prf' (SETEQ m S n T p mp np)) -> EL m S -> EL n T

coh : (m : Nat)(S : raise set m)(n : Nat)(T : raise set n) ->
      (p : Nat)(mp : Embedding m p)(np : Embedding n p) ->
      (Q : EL p (Prf' (SETEQ m S n T p mp np)))(s : EL m S) ->
      EL p (Prf' (VALEQ m S s n T (coe m S n T p mp np Q s) p mp np))

coe m (U' set) n (U' set) p mp np Q s =
  nsubst p m n Q (\ i -> uni (Level i) set) s
coe m (U' prop) n (U' prop) p mp np Q s =
  nsubst p m n Q (\ i -> uni (Level i) prop) s
coe m (U' set) n (U' prop) _ _ _ () _
coe m (U' prop) n (U' set) _ _ _ () _
coe m (U' _) n (Prf' P) p mp np () s
coe m (U' _) n (B' _) p mp np () s
coe m (U' _) n Two' p mp np () s
coe m (U' _) n (Pi' S T) p mp np () s
coe m (U' _) n (Sg' S T) p mp np () s
coe m (U' _) n (Wi' I S P r i) p mp np () s
coe m (U' _) ze (El' ()) p mp np Q s
coe m (U' set) (su n) (El' T) p mp np Q s =
  coe m (U' set) n T p mp (suEm np) Q s
coe m (U' prop) (su n) (El' T) p mp np Q s =
  coe m (U' prop) n T p mp (suEm np) Q s
coe m (Prf' P) n (U' y) p mp np () s
coe m (Prf' P) ze (El' ()) p mp np Q s
coe m (Prf' P) (su n) (El' T) p mp np Q s =
   coe m (Prf' P) n T p mp (suEm np) Q s
coe m (Prf' P) n (Prf' P') p mp np Q s =
  COE (Nop np prop P') (fst Q (EOC (Nop mp prop P) s))
coe m (Prf' P) n (B' y) p mp np () s
coe m (Prf' P) n Two' p mp np () s
coe m (Prf' P) n (Pi' S T) p mp np () s
coe m (Prf' P) n (Sg' S T) p mp np () s
coe m (Prf' P) n (Wi' I S P' r i) p mp np () s
coe m (B' b) n (U' y) p mp np () s
coe m (B' b) n (Prf' P) p mp np () s
coe m (B' b) n Two' p mp np () s
coe m (B' b) n (Pi' S T) p mp np () s
coe m (B' b) n (Sg' S T) p mp np () s
coe m (B' b) n (Wi' I S P r i) p mp np () s
coe m (B' b) n (B' c) p mp np Q s = bsubst b c Q s
coe m (B' b) ze (El' ()) p mp np Q s
coe m (B' b) (su n) (El' T) p mp np Q s = coe m (B' b) n T p mp (suEm np) Q s
coe m Two' n Two' p mp np Q s = s
coe m Two' n (U' y) p mp np () s
coe m Two' n (Prf' P) p mp np () s
coe m Two' n (B' y) p mp np () s
coe m Two' n (Pi' S T) p mp np () s
coe m Two' n (Sg' S T) p mp np () s
coe m Two' n (Wi' I S P r i) p mp np () s
coe m Two' ze (El' ()) p mp np Q s
coe m Two' (su n) (El' T) p mp np Q s = coe m Two' n T p mp (suEm np) Q s
coe m (Pi' S S') n (Pi' T T') p mp np Q f = help where
  help : (t : UpEl T) -> UpEl (T' t)
  help t = t' where
    s : EL m S
    s = coe n T m S p np mp (fst Q) t
    ts : EL p (Prf' (VALEQ n T t m S s p np mp))
    ts = coh n T m S p np mp (fst Q) t
    s' : EL m (S' s)
    s' = f s
    paf : (S0 : Set)(SQ : S0 == UpEl S) ->
          (T0 : Set)(TQ : T0 == UpEl T) ->
            ((t0 : T0)(s0 : S0) ->
             UpEl (VALEQ n T (COE TQ t0) m S (COE SQ s0) p np mp)
             ->
             UpEl (SETEQ m (S' (COE SQ s0)) n (T' (COE TQ t0)) p mp np)) ->
          UpEl (SETEQ m (S' s) n (T' t) p mp np)
    paf _ p1 _ p2 _ = _ -- H t s ts
    t' : EL n (T' t)
    t' = coe m (S' s) n (T' t) p mp np
             (paf (UpEl (Em mp set S)) (Nop mp set S)
                  (UpEl (Em np set T)) (Nop np set T)
                  (snd Q)) s'
coe m (Pi' S S') n (U' y) p mp np () s
coe m (Pi' S S') n (Prf' P) p mp np () s
coe m (Pi' S S') n (B' y) p mp np () s
coe m (Pi' S S') n Two' p mp np () s
coe m (Pi' S S') n (Sg' S0 T) p mp np () s
coe m (Pi' S S') n (Wi' I S0 P r i) p mp np () s
coe m (Pi' S S') ze (El' ()) p mp np Q s
coe m (Pi' S S') (su n) (El' T) p mp np Q s =
  coe m (Pi' S S') n T p mp (suEm np) Q s
coe m (Sg' S S') n (Sg' T T') p mp np Q x = pair t t' where
    s : EL m S
    s = fst x
    t : EL n T
    t = coe m S n T p mp np (fst Q) s
    st : EL p (Prf' (VALEQ m S s n T t p mp np))
    st = coh m S n T p mp np (fst Q) s
    s' : EL m (S' s)
    s' = snd x
    paf : (S0 : Set)(SQ : S0 == UpEl S) ->
          (T0 : Set)(TQ : T0 == UpEl T) ->
          ((s0 : S0) (t0 : T0)
          (s2
          : UpEl
           (VALEQ m S (COE SQ s0) n T (COE TQ t0) p mp
           np))
     ->
     UpEl (SETEQ m (S' (COE SQ s0)) n (T' (COE TQ t0)) p mp np)) ->
     UpEl (SETEQ m (S' s) n (T' t) p mp np)
    paf _ p1 _ p2 H = _ -- H s t st
    t' : EL n (T' t)
    t' = coe m (S' s) n (T' t) p mp np
         (paf (UpEl (Em mp set S)) (Nop mp set S)
              (UpEl (Em np set T)) (Nop np set T)
              (snd Q)) s'
coe m (Sg' S S') n (U' y) p mp np () s
coe m (Sg' S S') n (Prf' P) p mp np () s
coe m (Sg' S S') n (B' y) p mp np () s
coe m (Sg' S S') n Two' p mp np () s
coe m (Sg' S S') n (Pi' S0 T) p mp np () s
coe m (Sg' S S') n (Wi' I S0 P r i) p mp np () s
coe m (Sg' S S') ze (El' ()) p mp np Q s
coe m (Sg' S S') (su n) (El' T) p mp np Q s =
  coe m (Sg' S S') n T p mp (suEm np) Q s
coe m (Wi' I S P r i) n (Wi' J_ T R u j) p mp np Q s
  = shunt i s j (fst (snd Q)) where
    shunt : (i : UpEl I)(x : UpEl (Wi' I S P r i))
            (j : UpEl J_)(ij : UpEl (VALEQ m I i n J_ j p mp np)) ->
            UpEl (Wi' J_ T R u j)
    shunt i (wi s f) j ij = wi t g where
      paf : (I0 : Set)(IQ : I0 == UpEl I) ->
            (J0 : Set)(JQ : J0 == UpEl J_) ->
            ((i0 : I0) (j0 : J0) ->
                 (ij0 : UpEl (VALEQ m I (COE IQ i0) n J_ (COE JQ j0) p mp np)) ->
                 Sg (UpEl (SETEQ m (S (COE IQ i0)) n (T (COE JQ j0)) p mp np)) (\ ST ->
                 (s : UpEl (Em mp set (S (COE IQ i0))))
                 (t : UpEl (Em np set (T (COE JQ j0))))
                 (st : UpEl (VALEQ m (S (COE IQ i0)) (COE (Nop mp set (S (COE IQ i0))) s)
                                   n (T (COE JQ j0)) (COE (Nop np set (T (COE JQ j0))) t)
                             p mp np)) ->
                 Sg (UpEl (SETEQ n (R (COE JQ j0) (COE (Nop np set (T (COE JQ j0))) t))
                                 m (P (COE IQ i0) (COE (Nop mp set (S (COE IQ i0))) s))
                                 p np mp)) (\ RP ->
                 (l : UpEl (Em np set (R (COE JQ j0)
                            (COE (Nop np set (T (COE JQ j0))) t))))
                 (o : UpEl (Em mp set (P (COE IQ i0)
                            (COE (Nop mp set (S (COE IQ i0))) s))))
                 (lo : UpEl (VALEQ n (R (COE JQ j0) (COE (Nop np set (T (COE JQ j0))) t))
                                    (COE (Nop np set
                                          (R (COE JQ j0) (COE (Nop np set (T (COE JQ j0))) t)))
                                         l)
                                   m (P (COE IQ i0) (COE (Nop mp set (S (COE IQ i0))) s))
                                    (COE (Nop mp set
                                          (P (COE IQ i0) (COE (Nop mp set (S (COE IQ i0))) s)))
                                         o)
                                   p np mp)) ->
                 UpEl (VALEQ m I (r (COE IQ i0) (COE (Nop mp set (S (COE IQ i0))) s)
                                   (COE (Nop mp set
                                    (P (COE IQ i0) (COE (Nop mp set (S (COE IQ i0))) s))) o))
                             n J_ (u (COE JQ j0) (COE (Nop np set (T (COE JQ j0))) t)
                                   (COE (Nop np set
                                    (R (COE JQ j0) (COE (Nop np set (T (COE JQ j0))) t))) l))
                             p mp np)))) ->
            ((i1 : UpEl I) (j1 : UpEl J_) ->
                 (ij0 : UpEl (VALEQ m I i1 n J_ j1 p mp np)) ->
                 Sg (UpEl (SETEQ m (S i1) n (T j1) p mp np)) (\ ST ->
                 (s : UpEl (Em mp set (S i1)))
                 (t : UpEl (Em np set (T j1)))
                 (st : UpEl (VALEQ m (S i1) (COE (Nop mp set (S i1)) s)
                                   n (T j1) (COE (Nop np set (T j1)) t)
                             p mp np)) ->
                 Sg (UpEl (SETEQ n (R j1 (COE (Nop np set (T j1)) t))
                                 m (P i1 (COE (Nop mp set (S i1)) s))
                                 p np mp)) (\ RP ->
                 (l : UpEl (Em np set (R j1
                            (COE (Nop np set (T j1)) t))))
                 (o : UpEl (Em mp set (P i1
                            (COE (Nop mp set (S i1)) s))))
                 (lo : UpEl (VALEQ n (R j1 (COE (Nop np set (T j1)) t))
                                    (COE (Nop np set
                                          (R j1 (COE (Nop np set (T j1)) t)))
                                         l)
                                   m (P i1 (COE (Nop mp set (S i1)) s))
                                    (COE (Nop mp set
                                          (P i1 (COE (Nop mp set (S i1)) s)))
                                         o)
                                   p np mp)) ->
                 UpEl (VALEQ m I (r i1 (COE (Nop mp set (S i1)) s)
                                   (COE (Nop mp set
                                    (P i1 (COE (Nop mp set (S i1)) s))) o))
                             n J_ (u j1 (COE (Nop np set (T j1)) t)
                                   (COE (Nop np set
                                    (R j1 (COE (Nop np set (T j1)) t))) l))
                             p mp np))))
      paf _ p1 _ p2 H = _ -- H
      baf : _
      baf = paf (UpEl (Em mp set I)) (Nop mp set I)
                    (UpEl (Em np set J_)) (Nop np set J_)
                    (snd (snd Q)) i j ij
      t : UpEl (T j)
      t = coe m (S i) n (T j) p mp np (fst baf) s
      st : UpEl (VALEQ m (S i) s n (T j) t p mp np)
      st = coh m (S i) n (T j) p mp np (fst baf) s
      g : (l : UpEl (R j t)) -> UpEl (Wi' J_ T R u (u j t l))
      g l = shunt (r i s o) (f o) (u j t l) daf where
        qaf : (S0 : Set)(SQ : S0 == UpEl (S i)) ->
              (T0 : Set)(TQ : T0 == UpEl (T j)) ->
              ((s : S0)(t : T0)
               (st : UpEl (VALEQ m (S i) (COE SQ s) n (T j) (COE TQ t)
                             p mp np)) ->
               Sg (UpEl (SETEQ n (R j (COE TQ t)) m (P i (COE SQ s))
                            p np mp)) (\ RP ->
               (l : UpEl (Em np set (R j (COE TQ t))))
               (o : UpEl (Em mp set (P i (COE SQ s))))
               (lo : UpEl (VALEQ n (R j (COE TQ t))
                                    (COE (Nop np set (R j (COE TQ t))) l)
                                   m (P i (COE SQ s))
                                    (COE (Nop mp set (P i (COE SQ s))) o)
                                   p np mp)) ->
               UpEl (VALEQ m I (r i (COE SQ s)
                                   (COE (Nop mp set (P i (COE SQ s))) o))
                           n J_ (u j (COE TQ t)
                                   (COE (Nop np set (R j (COE TQ t))) l))
                           p mp np))) ->
              ((s : UpEl (S i))(t : UpEl (T j))
               (st : UpEl (VALEQ m (S i) s n (T j) t p mp np)) ->
               Sg (UpEl (SETEQ n (R j t) m (P i s) p np mp)) (\ RP ->
               (l : UpEl (Em np set (R j t)))
               (o : UpEl (Em mp set (P i s)))
               (lo : UpEl (VALEQ n (R j t) (COE (Nop np set (R j t)) l)
                                 m (P i s) (COE (Nop mp set (P i s)) o)
                                 p np mp)) ->
               UpEl (VALEQ m I (r i s (COE (Nop mp set (P i s)) o))
                           n J_ (u j t (COE (Nop np set (R j t)) l))
                           p mp np)))
        qaf _ p1 _ p2 H = _ -- H
        caf : _
        caf = qaf (UpEl (Em mp set (S i))) (Nop mp set (S i))
                  (UpEl (Em np set (T j))) (Nop np set (T j))
                  (snd baf) s t st
        o : UpEl (P i s)
        o = coe n (R j t) m (P i s) p np mp (fst caf) l
        lo : UpEl (VALEQ n (R j t) l m (P i s) o p np mp)
        lo = coh n (R j t) m (P i s) p np mp (fst caf) l
        raf : (P0 : Set)(PQ : P0 == UpEl (P i s)) ->
              (R0 : Set)(RQ : R0 == UpEl (R j t)) ->
              ((l : R0)(o : P0)
               (lo : UpEl (VALEQ n (R j t) (COE RQ l) m (P i s) (COE PQ o)
                                 p np mp)) ->
               UpEl (VALEQ m I (r i s (COE PQ o)) n J_ (u j t (COE RQ l))
                           p mp np)) ->
              ((l : UpEl (R j t))(o : UpEl (P i s))
               (lo : UpEl (VALEQ n (R j t) l m (P i s) o p np mp)) ->
               UpEl (VALEQ m I (r i s o) n J_ (u j t l) p mp np))
        raf _ p1 _ p2 H = _ -- H
        daf : _
        daf = raf (UpEl (Em mp set (P i s))) (Nop mp set (P i s))
                  (UpEl (Em np set (R j t))) (Nop np set (R j t))
                  (snd caf) l o lo
coe m (Wi' I S P r i) n (U' y) p mp np () s
coe m (Wi' I S P r i) n (Prf' P') p mp np () s
coe m (Wi' I S P r i) n (B' y) p mp np () s
coe m (Wi' I S P r i) n Two' p mp np () s
coe m (Wi' I S P r i) n (Pi' S' T) p mp np () s
coe m (Wi' I S P r i) n (Sg' S' T) p mp np () s
coe m (Wi' I S P r i) ze (El' ()) p mp np Q s
coe m (Wi' I S P r i) (su n) (El' T) p mp np Q s =
  coe m (Wi' I S P r i) n T p mp (suEm np) Q s
coe ze (El' ()) n T p mp np Q s
coe (su m) (El' S) n T p mp np Q s = coe m S n T p (suEm mp) np Q s

coh m S n T p mp np Q s =
  axiom p (VALEQ m S s n T (coe m S n T p mp np Q s) p mp np)
