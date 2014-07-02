-- TODO inference that agda can support and we don't:
--
--   PRF : (n : Nat) -> raise prop n -> raise set n
--   PRF n P = Prf' _ P -- one
--
-- And many variations of a metavariable that should be instantiated
-- with `one' as an argument of a a datacon of UpU (see U', Two').
--
--   COE : {S T : Set} -> S == T -> S -> T
--   COE p s = subst _ p s -- (\z -> z)
{-# OPTIONS --type-in-type #-}
module Hier where

open import Prelude

subst : {A : Set} {x y : A} (P : A -> Set) ->
        x == y -> P x -> P y
subst P = J (\ x y _ -> P x -> P y) (\ x p -> p)

postulate K : {A : Set} {x y : A}
              (P : (x : A) -> x == y -> Set) ->
              P y refl -> (p : x == y) -> P x p
-- K P x refl = x

sym' : {A : Set} (x y : A) -> x == y -> y == x
sym' x y p = J (\ x y p -> y == x) (\ _ -> refl) p

sym : {A : Set} {x y : A} -> x == y -> y == x
sym p = sym' _ _ p

Pi : (S : Set)(T : S -> Set) -> Set
Pi S T = (s : S) -> T s

record Sg (S : Set)(T : S -> Set) : Set
record Sg S T where
  constructor sg
  field
    fst : S
    snd : T fst
open Sg

-- data Wi (I : Set)(S : I -> Set)(P : (i : I) -> S i -> Set)
--         (r : (i : I)(s : S i) -> P i s -> I)(i : I) : Set
-- data Wi I S P r i where
--   wi : (s : S i) (f : (p : P i s) -> Wi I S P r (r i s p)) -> Wi I S P r i

Zero : Set
Zero = (A : Set) -> A

kill : {X : Set} -> Zero -> X
kill z = z _

record One : Set
record One where
  constructor one

data Two : Set
data Two where
  tt : Two
  ff : Two

Tt : Two -> Set
Tt tt = One
Tt ff = Zero

twoEq : Two -> Two -> Two
twoEq tt tt = tt
twoEq ff ff = tt
twoEq _  _  = ff

bsubst : (b c : Two) -> Tt (twoEq b c) -> Tt b -> Tt c
bsubst tt tt _ x = x
bsubst ff ff _ x = x
bsubst tt ff z x = kill z
bsubst ff tt z x = kill z

data Ki : Set
data Ki where
  set  : Ki
  prop : Ki

isSet : Ki -> Set
isSet set = One
isSet prop = Zero

record LEVEL : Set
record LEVEL where
  constructor level
  field
    uni  : Ki -> Set
    el   : (k : Ki) -> uni k -> Set
open LEVEL

data UpU (L : LEVEL)(k : Ki) : Set

UpEl' : (L : LEVEL)(k : Ki) -> UpU L k -> Set

UpEl : {L : LEVEL}{k : Ki} -> UpU L k -> Set
UpEl = UpEl' _ _

data UpU L k where
  U' : (q : isSet k) -> Ki -> UpU L k
  El' : (T : uni L k) -> UpU L k
  Prf' : (q : isSet k)(P : UpU L prop) -> UpU L k
  B' : Two -> UpU L k
  Two' : (q : isSet k) -> UpU L k
  Pi' : (S : UpU L set)(T : UpEl S -> UpU L k) -> UpU L k
  Sg' : (S : UpU L k)(T : UpEl S -> UpU L k) -> UpU L k
  -- Wi' : (I : UpU L set)
  --       (S : UpEl I ->  UpU L k)
  --       (P : (i : UpEl I)(s : UpEl (S i)) -> UpU L set)
  --       (r : (i : UpEl I)(s : UpEl (S i))(p : UpEl (P i s)) -> UpEl I)
  --       (i : UpEl I) -> UpU L k

UpEl' L _ (U' _ k) = uni L k
UpEl' L _ (El' T) = el L _ T
UpEl' _ _ (Prf' _ P) = UpEl' _ _ P
UpEl' _ _ (B' b) = Tt b
UpEl' _ _ (Two' _) = Two
UpEl' _ _ (Pi' S T) = Pi (UpEl' _ _ S) (\ s -> UpEl' _ _ (T s))
UpEl' _ _ (Sg' S T) = Sg (UpEl' _ _ S) (\ s -> UpEl' _ _ (T s))
-- UpEl' _ _ (Wi' I S P r i) =
--   Wi (UpEl' _ _ I) (\ i -> UpEl' _ _ (S i)) (\ i s -> UpEl' _ _ (P i s)) r i

data Nat : Set
data Nat where
  ze : Nat
  su : Nat -> Nat

Level : Nat -> LEVEL
Level ze     = level (\ _ -> Zero) (\ _ -> kill)
Level (su n) = level (UpU (Level n)) (UpEl' _)

raise : Ki -> Nat -> Set
raise k n = UpU (Level n) k

EL : (n : Nat) -> raise set n -> Set
EL n T = UpEl' (Level n) _ T

PRF : (n : Nat) -> raise prop n -> raise set n
PRF n P = Prf' one P

natEq : (n : Nat) -> Nat -> Nat -> raise prop n
natEq _ ze     ze     = (B' tt)
natEq p (su m) (su n) = natEq p m n
natEq _ _      _      = B' ff

nsubst : (p m n : Nat) -> EL p (PRF p (natEq p m n )) ->
         (P : Nat -> Set) -> P m -> P n
nsubst p ze     ze     _ P x = x
nsubst p ze     (su n) z _ _ = kill z
nsubst p (su m) ze     z _ _ = kill z
nsubst p (su m) (su n) q P x = nsubst p m n q (\ i -> P (su i)) x

record Embedding (m n : Nat) : Set
record Embedding m n where
  constructor embed
  field
    Em  : (k : Ki) -> raise k m ->  raise k n
    Nop : (k : Ki)(T : raise k m) -> UpEl (Em k T) == UpEl T
open Embedding

idEm : {n : Nat} -> Embedding n n
idEm = embed (\ k T -> T) (\ k T -> refl)

suEm : {m n : Nat} -> Embedding (su m) n -> Embedding m n
suEm em = embed (\ k T -> Em em k (El' T)) (\ k T -> Nop em k (El' T))

COE : {S T : Set} -> S == T -> S -> T
COE p s = subst (\ z -> z) p s

EOC : {S T : Set} -> S == T -> T -> S
EOC p s = subst (\ z -> z) (sym p) s

times : {k : Ki}(n : Nat) -> raise k n -> raise k n -> raise k n
times _ P Q = Sg' P (\ _ -> Q)

fun : (n : Nat) -> raise prop n -> raise prop n -> raise prop n
fun _ P Q = Pi' (Prf' one P) (\ _ -> Q)

upPi' : {k : Ki}{n p : Nat}(E : Embedding n p) ->
        (S : raise set n) -> (EL n S -> raise k p) -> raise k p
upPi' E S T = Pi' (Em E set S) (\ s' -> T (COE (Nop E set S) s'))

PROPEQ : (m : Nat)(P : raise prop m)(n : Nat)(Q : raise prop n) ->
         (p : Nat)(mp : Embedding m p)(np : Embedding n p) ->
         raise prop p
PROPEQ m P n Q p mp np =
  times p (fun p (Em mp prop P) (Em np prop Q))
          (fun p (Em np prop Q) (Em mp prop P))

SETEQ : (m : Nat)(S : raise set m)(n : Nat)(T : raise set n) ->
        (p : Nat)(mp : Embedding m p)(np : Embedding n p) ->
        raise prop p

VALEQ : (m : Nat)(S : raise set m)(s : EL m S)
        (n : Nat)(T : raise set n)(t : EL n T) ->
        (p : Nat)(mp : Embedding m p)(np : Embedding n p) ->
        raise prop p

SETEQ m (U' _ _) n (Prf' _ _) _ _ _ = (B' ff)
SETEQ m (U' _ _) n (B' _) _ _ _ = (B' ff)
SETEQ m (U' _ _) n (Two' _) _ _ _ = (B' ff)
SETEQ m (U' _ _) n (Pi' _ _) _ _ _ = (B' ff)
SETEQ m (U' _ _) n (Sg' _ _) _ _ _ = (B' ff)
-- SETEQ m (U' _ _) n (Wi' _ _ _ _ _) _ _ _ = (B' ff)
SETEQ m (U' _ set) n (U' _ set) p mp np = natEq p m n
SETEQ m (U' _ prop) n (U' _ prop) p mp np = natEq p m n
SETEQ m (U' _ _) n (U' _ _) _ _ _ = (B' ff)
SETEQ m (Prf' _ P) n (Prf' _ Q) p mp np = PROPEQ m P n Q p mp np
SETEQ m (Prf' _ P) n (U' _ _) _ _ _ = B' ff
SETEQ m (Prf' _ P) n (B' _) _ _ _ = B' ff
SETEQ m (Prf' _ P) n (Two' _) _ _ _ = B' ff
SETEQ m (Prf' _ P) n (Pi' _ _) _ _ _ = B' ff
SETEQ m (Prf' _ P) n (Sg' _ _) _ _ _ = B' ff
-- SETEQ m (Prf' _ P) n (Wi' _ _ _ _ _) _ _ _ = B' ff
SETEQ m (B' b) n (B' c) p mp np = B' (twoEq b c)
SETEQ m (B' b) n (U' _ _) _ _ _ = B' ff
SETEQ m (B' b) n (Prf' _ _) _ _ _ = B' ff
SETEQ m (B' b) n (Two' _) _ _ _ = B' ff
SETEQ m (B' b) n (Pi' _ _) _ _ _ = B' ff
SETEQ m (B' b) n (Sg' _ _) _ _ _ = B' ff
-- SETEQ m (B' b) n (Wi' _ _ _ _ _) _ _ _ = B' ff
SETEQ m (Two' _) n (Two' _) p mp np = (B' tt)
SETEQ m (Two' _) n (U' _ _) _ _ _ = B' ff
SETEQ m (Two' _) n (Prf' _ _) _ _ _ = B' ff
SETEQ m (Two' _) n (B' b) _ _ _ = B' ff
SETEQ m (Two' _) n (Pi' _ _) _ _ _ = B' ff
SETEQ m (Two' _) n (Sg' _ _) _ _ _ = B' ff
-- SETEQ m (Two' _) n (Wi' _ _ _ _ _) _ _ _ = B' ff
SETEQ m (Pi' S S') n (Pi' T T') p mp np =
  times p
    (SETEQ n T m S p np mp)
    (upPi' np T (\ t ->
       upPi' mp S (\ s ->
         fun p (VALEQ n T t m S s p np mp) (SETEQ m (S' s) n (T' t) p mp np))))
SETEQ m (Pi' S S') n (U' _ _) _ _ _ = B' ff
SETEQ m (Pi' S S') n (Prf' _ _) _ _ _ = B' ff
SETEQ m (Pi' S S') n (B' b) _ _ _ = B' ff
SETEQ m (Pi' S S') n (Sg' _ _) _ _ _ = B' ff
SETEQ m (Pi' S S') n (Two' _) _ _ _ = B' ff
-- SETEQ m (Pi' S S') n (Wi' _ _ _ _ _) _ _ _ = B' ff
SETEQ m (Sg' S S') n (Sg' T T') p mp np =
  times p
    (SETEQ m S n T p mp np)
    (upPi' mp S (\ s ->
     upPi' np T (\ t ->
     fun p (VALEQ m S s n T t p mp np)
           (SETEQ m (S' s) n (T' t) p mp np))))
SETEQ m (Sg' S S') n (U' _ _) _ _ _ = B' ff
SETEQ m (Sg' S S') n (Prf' _ _) _ _ _ = B' ff
SETEQ m (Sg' S S') n (B' b) _ _ _ = B' ff
SETEQ m (Sg' S S') n (Pi' _ _) _ _ _ = B' ff
SETEQ m (Sg' S S') n (Two' _) _ _ _ = B' ff
-- SETEQ m (Sg' S S') n (Wi' _ _ _ _ _) _ _ _ = B' ff
-- SETEQ m (Wi' I S P r i) n (Wi' J' T Q u j) p mp np =
--   times p
--     (SETEQ m I n J' p mp np)
--     (times p
--        (VALEQ m I i n J' j p mp np)
--         (upPi' mp I (\ i ->
--          upPi' np J' (\ j ->
--          fun p
--            (VALEQ m I i n J' j p mp np)
--            (times p
--               (SETEQ m (S i) n (T j) p mp np)
--               (upPi' mp (S i) (\ s -> upPi' np (T j) (\ t ->
--                fun p
--                  (VALEQ m (S i) s n (T j) t p mp np)
--                  (times p
--                     (SETEQ n (Q j t) m (P i s) p np mp)
--                     (upPi' np (Q j t) (\ q -> upPi' mp (P i s) (\ o ->
--                      fun p (VALEQ n (Q j t) q m (P i s) o p np mp)
--                            (VALEQ m I (r i s o) n J' (u j t q) p mp np)))))))))))))
-- SETEQ m (Wi' _ _ _ _ _) n (U' _ _) _ _ _ = B' ff
-- SETEQ m (Wi' _ _ _ _ _) n (Prf' _ _) _ _ _ = B' ff
-- SETEQ m (Wi' _ _ _ _ _) n (B' b) _ _ _ = B' ff
-- SETEQ m (Wi' _ _ _ _ _) n (Pi' _ _) _ _ _ = B' ff
-- SETEQ m (Wi' _ _ _ _ _) n (Two' _) _ _ _ = B' ff
-- SETEQ m (Wi' _ _ _ _ _) n (Sg' _ _) _ _ _ = B' ff
SETEQ ze (El' z) n T p mp np = kill z
SETEQ (su m) (El' S) n T p mp np = SETEQ m S n T p (suEm mp) np
SETEQ m S ze (El' z) p mp np = kill z
SETEQ m S (su n) (El' T) p mp np = SETEQ m S n T p mp (suEm np)

VALEQ m (Two' _) tt n (Two' _) ff p mp np = B' ff
VALEQ m (Two' _) ff n (Two' _) tt p mp np = B' ff
VALEQ m (Pi' S S') f n (Pi' T T') g p mp np =
  upPi' mp S (\ s -> upPi' np T (\ t ->
  fun p
    (VALEQ m S s n T t p mp np)
    (VALEQ m (S' s) (f s) n (T' t) (g t) p mp np)))
VALEQ m (Sg' S S') s n (Sg' T T') t p mp np =
  times p
    (VALEQ m S (fst s) n T (fst t) p mp np)
    (VALEQ m (S' (fst s)) (snd s) n (T' (fst t)) (snd t) p mp np)
-- VALEQ m (Wi' I S P r i) s n (Wi' J' T Q u j) t p mp np =
--   WEQ i s j t where
--   WEQ : (i : EL m I)(s : EL m (Wi' I S P r i))
--         (j : EL n J')(t : EL n (Wi' J' T Q u j)) -> raise prop p
--   WEQ i (wi s f) j (wi t g) =
--     times p
--       (VALEQ m (S i) s n (T j) t p mp np)
--       (upPi' mp (P i s) (\ p -> upPi' np (Q j t) (\ q -> 
--        WEQ (r i s p) (f p) (u j t q) (g q))))
VALEQ ze (U' _ _) z n (U' _ _) t p mp np = kill z
VALEQ (su y) (U' _ _) s ze (U' _ _) z p mp np = kill z
VALEQ (su m) (U' _ set) S (su n) (U' _ set) T p mp np =
  SETEQ m S n T p (suEm mp) (suEm np)
VALEQ (su m) (U' _ prop) P (su n) (U' _ prop) Q p mp np =
  PROPEQ m P n Q p (suEm mp) (suEm np)
VALEQ ze (El' z) s n T t p mp np = kill z
VALEQ (su m) (El' S) s n T t p mp np =
  VALEQ m S s n T t p (suEm mp) np
VALEQ m S s ze (El' z) t p mp np = kill z
VALEQ m S s (su n) (El' T) t p mp np =
  VALEQ m S s n T t p mp (suEm np)
VALEQ m _ s n _ t p mp np = B' tt

postulate axiom : (p : Nat)(P : raise prop p) -> EL p (Prf' one P)


coe : (m : Nat)(S : raise set m)(n : Nat)(T : raise set n) ->
      (p : Nat)(mp : Embedding m p)(np : Embedding n p) ->
      EL p (Prf' one (SETEQ m S n T p mp np)) -> EL m S -> EL n T

coh : (m : Nat)(S : raise set m)(n : Nat)(T : raise set n) ->
      (p : Nat)(mp : Embedding m p)(np : Embedding n p) ->
      (Q : EL p (Prf' one (SETEQ m S n T p mp np)))(s : EL m S) ->
      EL p (Prf' one (VALEQ m S s n T (coe m S n T p mp np Q s) p mp np))

coe m (U' _ set) n (U' _ set) p mp np Q s =
  nsubst p m n Q (\ i -> uni (Level i) set) s
coe m (U' _ prop) n (U' _ prop) p mp np Q s =
  nsubst p m n Q (\ i -> uni (Level i) prop) s
coe m (U' _ set) n (U' _ prop) _ _ _ z _ = kill z
coe m (U' _ prop) n (U' _ set) _ _ _ z _ = kill z
coe m (U' _ _) n (Prf' _ P) p mp np z s = kill z
coe m (U' _ _) n (B' _) p mp np z s = kill z
coe m (U' _ _) n (Two' _) p mp np z s = kill z
coe m (U' _ _) n (Pi' S T) p mp np z s = kill z
coe m (U' _ _) n (Sg' S T) p mp np z s = kill z
-- coe m (U' _ _) n (Wi' I S P r i) p mp np z s = kill z
coe m (U' _ _) ze (El' z) p mp np Q s = kill z
coe m (U' _ set) (su n) (El' T) p mp np Q s =
  coe m (U' one set) n T p mp (suEm np) Q s
coe m (U' _ prop) (su n) (El' T) p mp np Q s =
  -- TODO in Agda we can use `U' _'
  coe m (U' one prop) n T p mp (suEm np) Q s
coe m (Prf' _ P) n (U' _ y) p mp np z s = kill z
coe m (Prf' _ P) ze (El' z) p mp np Q s = kill z
coe m (Prf' _ P) (su n) (El' T) p mp np Q s =
  coe m (Prf' one P) n T p mp (suEm np) Q s
coe m (Prf' _ P) n (Prf' _ P') p mp np Q s =
  COE (Nop np prop P') (fst Q (EOC (Nop mp prop P) s))
coe m (Prf' _ P) n (B' y) p mp np z s = kill z
coe m (Prf' _ P) n (Two' _) p mp np z s = kill z
coe m (Prf' _ P) n (Pi' S T) p mp np z s = kill z
coe m (Prf' _ P) n (Sg' S T) p mp np z s = kill z
-- coe m (Prf' _ P) n (Wi' I S P' r i) p mp np z s = kill z
coe m (B' b) n (U' _ y) p mp np z s = kill z
coe m (B' b) n (Prf' _ P) p mp np z s = kill z
coe m (B' b) n (Two' _) p mp np z s = kill z
coe m (B' b) n (Pi' S T) p mp np z s = kill z
coe m (B' b) n (Sg' S T) p mp np z s = kill z
-- coe m (B' b) n (Wi' I S P r i) p mp np z s = kill z
coe m (B' b) n (B' c) p mp np Q s = bsubst b c Q s
coe m (B' b) ze (El' z) p mp np Q s = kill z
coe m (B' b) (su n) (El' T) p mp np Q s = coe m (B' b) n T p mp (suEm np) Q s
coe m (Two' _) n (Two' _) p mp np Q s = s
coe m (Two' _) n (U' _ y) p mp np z s = kill z
coe m (Two' _) n (Prf' _ P) p mp np z s = kill z
coe m (Two' _) n (B' y) p mp np z s = kill z
coe m (Two' _) n (Pi' S T) p mp np z s = kill z
coe m (Two' _) n (Sg' S T) p mp np z s = kill z
-- coe m (Two' one) n (Wi' I S P r i) p mp np z s = kill z
coe m (Two' _) ze (El' z) p mp np Q s = kill z
coe m (Two' _) (su n) (El' T) p mp np Q s = coe m (Two' one) n T p mp (suEm np) Q s
coe m (Pi' S S') n (Pi' T T') p mp np Q f = help where
  help : (t : UpEl T) -> UpEl (T' t)
  help t = t' where
    s : EL m S
    s = coe n T m S p np mp (fst Q) t
    ts : EL p (Prf' one (VALEQ n T t m S s p np mp))
    ts = coh n T m S p np mp (fst Q) t
    s' : EL m (S' s)
    s' = f s
    Paf : (S0 : Set)(SQ : S0 == UpEl S)(T0 : Set)(TQ : T0 == UpEl T) -> Set
    Paf S0 SQ T0 TQ =
      ((t0 : T0)(s0 : S0) ->
       UpEl (VALEQ n T (COE TQ t0) m S (COE SQ s0) p np mp) ->
       UpEl (SETEQ m (S' (COE SQ s0)) n (T' (COE TQ t0)) p mp np)) ->
      UpEl (SETEQ m (S' s) n (T' t) p mp np)
    paf : (S0 : Set)(SQ : S0 == UpEl S) ->
          (T0 : Set)(TQ : T0 == UpEl T) ->
          Paf S0 SQ T0 TQ
    paf S0 SQ T0 TQ =
      K (\S0 SQ -> Paf S0 SQ T0 TQ)
        (K (\T0 TQ -> Paf (UpEl S) refl T0 TQ) (\H -> H t s ts) TQ)
        SQ
    t' : EL n (T' t)
    t' = coe m (S' s) n (T' t) p mp np
             (paf (UpEl (Em mp set S)) (Nop mp set S)
                  (UpEl (Em np set T)) (Nop np set T)
                  (snd Q)) s'
coe m (Pi' S S') n (U' _ y) p mp np z s = kill z
coe m (Pi' S S') n (Prf' _ P) p mp np z s = kill z
coe m (Pi' S S') n (B' y) p mp np z s = kill z
coe m (Pi' S S') n (Two' _) p mp np z s = kill z
coe m (Pi' S S') n (Sg' S0 T) p mp np z s = kill z
-- coe m (Pi' S S') n (Wi' I S0 P r i) p mp np z s = kill z
coe m (Pi' S S') ze (El' z) p mp np Q s = kill z
coe m (Pi' S S') (su n) (El' T) p mp np Q s =
  coe m (Pi' S S') n T p mp (suEm np) Q s
coe m (Sg' S S') n (Sg' T T') p mp np Q x =  sg t t' where
    s : EL m S
    s = fst x
    t : EL n T
    t = coe m S n T p mp np (fst Q) s
    st : EL p (Prf' one (VALEQ m S s n T t p mp np))
    st = coh m S n T p mp np (fst Q) s
    s' : EL m (S' s)
    s' = snd x
    Paf : (S0 : Set)(SQ : S0 == UpEl S)
          (T0 : Set)(TQ : T0 == UpEl T) ->
          Set
    Paf S0 SQ T0 TQ =
      ((s0 : S0) (t0 : T0)
       (s2 : UpEl (VALEQ m S (COE SQ s0) n T (COE TQ t0) p mp np)) ->
       UpEl (SETEQ m (S' (COE SQ s0)) n (T' (COE TQ t0)) p mp np)) ->
      UpEl (SETEQ m (S' s) n (T' t) p mp np)
    paf : (S0 : Set)(SQ : S0 == UpEl S) ->
          (T0 : Set)(TQ : T0 == UpEl T) ->
          Paf S0 SQ T0 TQ
    paf S0 SQ T0 TQ =
      K (\S0 SQ -> Paf S0 SQ T0 TQ)
        (K (\T0 TQ -> Paf (UpEl S) refl T0 TQ) (\H -> H s t st) TQ)
        SQ
    t' : EL n (T' t)
    t' = coe m (S' s) n (T' t) p mp np
         (paf (UpEl (Em mp set S)) (Nop mp set S)
              (UpEl (Em np set T)) (Nop np set T)
              (snd Q)) s'
coe m (Sg' S S') n (U' _ y) p mp np z s = kill z
coe m (Sg' S S') n (Prf' _ P) p mp np z s = kill z
coe m (Sg' S S') n (B' y) p mp np z s = kill z
coe m (Sg' S S') n (Two' _) p mp np z s = kill z
coe m (Sg' S S') n (Pi' S0 T) p mp np z s = kill z
-- coe m (Sg' S S') n (Wi' I S0 P r i) p mp np z s = kill z
coe m (Sg' S S') ze (El' z) p mp np Q s = kill z
coe m (Sg' S S') (su n) (El' T) p mp np Q s =
  coe m (Sg' S S') n T p mp (suEm np) Q s
-- coe m (Wi' I S P r i) n (Wi' J' T R u j) p mp np Q s
--   = shunt i s j (fst (snd Q)) where
--     shunt : (i : UpEl I)(x : UpEl (Wi' I S P r i))
--             (j : UpEl J')(ij : UpEl (VALEQ m I i n J' j p mp np)) ->
--             UpEl (Wi' J' T R u j)
--     shunt i (wi s f) j ij = wi t g where
--       Paf : (I0 : Set)(IQ : I0 == UpEl I) ->
--             (J0 : Set)(JQ : J0 == UpEl J') ->
--             Set
--       Paf I0 IQ J0 JQ =
--             ((i0 : I0) (j0 : J0) ->
--                -- TODO replace (COE IQ i0) with i1 and (COE JQ j0) with
--                -- j1 when we have let.
--                    (ij0 : UpEl (VALEQ m I (COE IQ i0) n J' (COE JQ j0) p mp np)) ->
--                    Sg (UpEl (SETEQ m (S (COE IQ i0)) n (T (COE JQ j0)) p mp np)) (\ ST ->
--                    (s : UpEl (Em mp set (S (COE IQ i0))))
--                    (t : UpEl (Em np set (T (COE JQ j0))))
--                    (st : UpEl (VALEQ m (S (COE IQ i0)) (COE (Nop mp set (S (COE IQ i0))) s)
--                                      n (T (COE JQ j0)) (COE (Nop np set (T (COE JQ j0))) t)
--                                p mp np)) ->
--                    Sg (UpEl (SETEQ n (R (COE JQ j0) (COE (Nop np set (T (COE JQ j0))) t))
--                                    m (P (COE IQ i0) (COE (Nop mp set (S (COE IQ i0))) s))
--                                    p np mp)) (\ RP ->
--                    (l : UpEl (Em np set (R (COE JQ j0)
--                               (COE (Nop np set (T (COE JQ j0))) t))))
--                    (o : UpEl (Em mp set (P (COE IQ i0)
--                               (COE (Nop mp set (S (COE IQ i0))) s))))
--                    (lo : UpEl (VALEQ n (R (COE JQ j0) (COE (Nop np set (T (COE JQ j0))) t))
--                                       (COE (Nop np set
--                                             (R (COE JQ j0) (COE (Nop np set (T (COE JQ j0))) t)))
--                                            l)
--                                      m (P (COE IQ i0) (COE (Nop mp set (S (COE IQ i0))) s))
--                                       (COE (Nop mp set
--                                             (P (COE IQ i0) (COE (Nop mp set (S (COE IQ i0))) s)))
--                                            o)
--                                      p np mp)) ->
--                    UpEl (VALEQ m I (r (COE IQ i0) (COE (Nop mp set (S (COE IQ i0))) s)
--                                      (COE (Nop mp set
--                                       (P (COE IQ i0) (COE (Nop mp set (S (COE IQ i0))) s))) o))
--                                n J' (u (COE JQ j0) (COE (Nop np set (T (COE JQ j0))) t)
--                                      (COE (Nop np set
--                                       (R (COE JQ j0) (COE (Nop np set (T (COE JQ j0))) t))) l))
--                                p mp np)))) ->
--               ((i1 : UpEl I) (j1 : UpEl J') ->
--                    (ij0 : UpEl (VALEQ m I i1 n J' j1 p mp np)) ->
--                    Sg (UpEl (SETEQ m (S i1) n (T j1) p mp np)) (\ ST ->
--                    (s : UpEl (Em mp set (S i1)))
--                    (t : UpEl (Em np set (T j1)))
--                    (st : UpEl (VALEQ m (S i1) (COE (Nop mp set (S i1)) s)
--                                      n (T j1) (COE (Nop np set (T j1)) t)
--                                p mp np)) ->
--                    Sg (UpEl (SETEQ n (R j1 (COE (Nop np set (T j1)) t))
--                                    m (P i1 (COE (Nop mp set (S i1)) s))
--                                    p np mp)) (\ RP ->
--                    (l : UpEl (Em np set (R j1
--                               (COE (Nop np set (T j1)) t))))
--                    (o : UpEl (Em mp set (P i1
--                               (COE (Nop mp set (S i1)) s))))
--                    (lo : UpEl (VALEQ n (R j1 (COE (Nop np set (T j1)) t))
--                                       (COE (Nop np set
--                                             (R j1 (COE (Nop np set (T j1)) t)))
--                                            l)
--                                      m (P i1 (COE (Nop mp set (S i1)) s))
--                                       (COE (Nop mp set
--                                             (P i1 (COE (Nop mp set (S i1)) s)))
--                                            o)
--                                      p np mp)) ->
--                    UpEl (VALEQ m I (r i1 (COE (Nop mp set (S i1)) s)
--                                      (COE (Nop mp set
--                                       (P i1 (COE (Nop mp set (S i1)) s))) o))
--                                n J' (u j1 (COE (Nop np set (T j1)) t)
--                                      (COE (Nop np set
--                                       (R j1 (COE (Nop np set (T j1)) t))) l))
--                                p mp np))))
--       paf : (I0 : Set)(IQ : I0 == UpEl I) ->
--             (J0 : Set)(JQ : J0 == UpEl J') ->
--             Paf I0 IQ J0 JQ
--       paf I0 IQ J0 JQ =
--         K (\I0 IQ -> Paf I0 IQ J0 JQ)
--           (K (\J0 JQ -> Paf (UpEl I) refl J0 JQ) (\H -> H) JQ)
--           IQ
--       baf : _
--       baf = paf (UpEl (Em mp set I)) (Nop mp set I)
--                     (UpEl (Em np set J')) (Nop np set J')
--                     (snd (snd Q)) i j ij
--       t : UpEl (T j)
--       t = coe m (S i) n (T j) p mp np (fst baf) s
--       st : UpEl (VALEQ m (S i) s n (T j) t p mp np)
--       st = coh m (S i) n (T j) p mp np (fst baf) s
--       g : (l : UpEl (R j t)) -> UpEl (Wi' J' T R u (u j t l))
--       g l = shunt (r i s o) (f o) (u j t l) daf where
--         Qaf : (S0 : Set)(SQ : S0 == UpEl (S i)) ->
--               (T0 : Set)(TQ : T0 == UpEl (T j)) ->
--               Set
--         Qaf S0 SQ T0 TQ =
--               ((s : S0)(t : T0)
--                (st : UpEl (VALEQ m (S i) (COE SQ s) n (T j) (COE TQ t)
--                              p mp np)) ->
--                Sg (UpEl (SETEQ n (R j (COE TQ t)) m (P i (COE SQ s))
--                             p np mp)) (\ RP ->
--                (l : UpEl (Em np set (R j (COE TQ t))))
--                (o : UpEl (Em mp set (P i (COE SQ s))))
--                (lo : UpEl (VALEQ n (R j (COE TQ t))
--                                     (COE (Nop np set (R j (COE TQ t))) l)
--                                    m (P i (COE SQ s))
--                                     (COE (Nop mp set (P i (COE SQ s))) o)
--                                    p np mp)) ->
--                UpEl (VALEQ m I (r i (COE SQ s)
--                                    (COE (Nop mp set (P i (COE SQ s))) o))
--                            n J' (u j (COE TQ t)
--                                    (COE (Nop np set (R j (COE TQ t))) l))
--                            p mp np))) ->
--               ((s : UpEl (S i))(t : UpEl (T j))
--                (st : UpEl (VALEQ m (S i) s n (T j) t p mp np)) ->
--                Sg (UpEl (SETEQ n (R j t) m (P i s) p np mp)) (\ RP ->
--                (l : UpEl (Em np set (R j t)))
--                (o : UpEl (Em mp set (P i s)))
--                (lo : UpEl (VALEQ n (R j t) (COE (Nop np set (R j t)) l)
--                                  m (P i s) (COE (Nop mp set (P i s)) o)
--                                  p np mp)) ->
--                UpEl (VALEQ m I (r i s (COE (Nop mp set (P i s)) o))
--                            n J' (u j t (COE (Nop np set (R j t)) l))
--                            p mp np)))
--         qaf : (S0 : Set)(SQ : S0 == UpEl (S i)) ->
--               (T0 : Set)(TQ : T0 == UpEl (T j)) ->
--               Qaf S0 SQ T0 TQ
--         qaf S0 SQ T0 TQ =
--           K (\S0 SQ -> Qaf S0 SQ T0 TQ)
--             (K (\T0 TQ -> Qaf (UpEl (S i)) refl T0 TQ) (\H -> H) TQ)
--             SQ
--         caf : _
--         caf = qaf (UpEl (Em mp set (S i))) (Nop mp set (S i))
--                   (UpEl (Em np set (T j))) (Nop np set (T j))
--                   (snd baf) s t st
--         o : UpEl (P i s)
--         o = coe n (R j t) m (P i s) p np mp (fst caf) l
--         lo : UpEl (VALEQ n (R j t) l m (P i s) o p np mp)
--         lo = coh n (R j t) m (P i s) p np mp (fst caf) l
--         Raf : (P0 : Set)(PQ : P0 == UpEl (P i s)) ->
--               (R0 : Set)(RQ : R0 == UpEl (R j t)) ->
--               Set
--         Raf P0 PQ R0 RQ =
--               ((l : R0)(o : P0)
--                (lo : UpEl (VALEQ n (R j t) (COE RQ l) m (P i s) (COE PQ o)
--                                  p np mp)) ->
--                UpEl (VALEQ m I (r i s (COE PQ o)) n J' (u j t (COE RQ l))
--                            p mp np)) ->
--               ((l : UpEl (R j t))(o : UpEl (P i s))
--                (lo : UpEl (VALEQ n (R j t) l m (P i s) o p np mp)) ->
--                UpEl (VALEQ m I (r i s o) n J' (u j t l) p mp np))
--         raf : (P0 : Set)(PQ : P0 == UpEl (P i s)) ->
--               (R0 : Set)(RQ : R0 == UpEl (R j t)) ->
--               Raf P0 PQ R0 RQ
--         raf P0 PQ R0 RQ =
--           K (\P0 PQ -> Raf P0 PQ R0 RQ)
--             (K (\R0 RQ -> Raf (UpEl (P i s)) refl R0 RQ) (\H -> H) RQ)
--             PQ
--         daf : _
--         daf = raf (UpEl (Em mp set (P i s))) (Nop mp set (P i s))
--                   (UpEl (Em np set (R j t))) (Nop np set (R j t))
--                   (snd caf) l o lo
-- coe m (Wi' I S P r i) n (U' _ y) p mp np z s = kill z
-- coe m (Wi' I S P r i) n (Prf' _ P') p mp np z s = kill z
-- coe m (Wi' I S P r i) n (B' y) p mp np z s = kill z
-- coe m (Wi' I S P r i) n (Two' _) p mp np z s = kill z
-- coe m (Wi' I S P r i) n (Pi' S' T) p mp np z s = kill z
-- coe m (Wi' I S P r i) n (Sg' S' T) p mp np z s = kill z
-- coe m (Wi' I S P r i) ze (El' z) p mp np Q s = kill z
-- coe m (Wi' I S P r i) (su n) (El' T) p mp np Q s =
--   coe m (Wi' I S P r i) n T p mp (suEm np) Q s
coe ze (El' z) n T p mp np Q s = kill z
coe (su m) (El' S) n T p mp np Q s = coe m S n T p (suEm mp) np Q s

coh m S n T p mp np Q s =
  axiom p (VALEQ m S s n T (coe m S n T p mp np Q s) p mp np)
