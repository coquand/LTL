{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Prelude -- the small amount of infrastructure beyond LTL.Base that the
-- development needs: boolean conjunction with its two elimination lemmas,
-- soundness/reflexivity of natEq, binary sums, lists with membership, and the
-- index/nth round-trip of FORMALISATION-PLAN.md G2.

module LTL.Prelude where

open import LTL.Base public

------------------------------------------------------------------------
-- Boolean conjunction

boolAnd : Bool -> Bool -> Bool
boolAnd true  b = b
boolAnd false b = false

andTrueL : (a b : Bool) -> Eq (boolAnd a b) true -> Eq a true
andTrueL true  b p = refl
andTrueL false b ()

andTrueR : (a b : Bool) -> Eq (boolAnd a b) true -> Eq b true
andTrueR true  b p = p
andTrueR false b ()

andIntro : (a b : Bool) -> Eq a true -> Eq b true -> Eq (boolAnd a b) true
andIntro true  b p q = q
andIntro false b () q

boolNot : Bool -> Bool
boolNot true  = false
boolNot false = true

boolImp : Bool -> Bool -> Bool
boolImp true  b = b
boolImp false b = true

boolOr : Bool -> Bool -> Bool
boolOr true  b = true
boolOr false b = b

boolEq : Bool -> Bool -> Bool
boolEq true  b = b
boolEq false b = boolNot b

------------------------------------------------------------------------
-- natEq

natEq_refl : (n : Nat) -> Eq (natEq n n) true
natEq_refl zero    = refl
natEq_refl (suc n) = natEq_refl n

natEq_sound : (n m : Nat) -> Eq (natEq n m) true -> Eq n m
natEq_sound zero    zero    p = refl
natEq_sound zero    (suc m) ()
natEq_sound (suc n) zero    ()
natEq_sound (suc n) (suc m) p = eqCong suc (natEq_sound n m p)

sucInj : {n m : Nat} -> Eq (suc n) (suc m) -> Eq n m
sucInj refl = refl

------------------------------------------------------------------------
-- Sums

data Sum (A B : Set) : Set where
  inl : A -> Sum A B
  inr : B -> Sum A B

sumElim : {A B C : Set} -> (A -> C) -> (B -> C) -> Sum A B -> C
sumElim f g (inl a) = f a
sumElim f g (inr b) = g b

------------------------------------------------------------------------
-- Strict order on Nat, needed to index into sub P

data Lt : Nat -> Nat -> Set where
  ltZero : {n : Nat}              -> Lt zero (suc n)
  ltSuc  : {n m : Nat} -> Lt n m -> Lt (suc n) (suc m)

------------------------------------------------------------------------
-- Sigma and products

data Sigma (A : Set) (B : A -> Set) : Set where
  sig : (x : A) -> B x -> Sigma A B

data Prod (A B : Set) : Set where
  prod : A -> B -> Prod A B

prodFst : {A B : Set} -> Prod A B -> A
prodFst (prod a b) = a

prodSnd : {A B : Set} -> Prod A B -> B
prodSnd (prod a b) = b

------------------------------------------------------------------------
-- Reading a false boolean backwards

andFalse : (a b : Bool) -> Eq (boolAnd a b) false -> Sum (Eq a false) (Eq b false)
andFalse true  b e = inr e
andFalse false b e = inl refl

boolNot_not : (b : Bool) -> Eq (boolNot (boolNot b)) b
boolNot_not true  = refl
boolNot_not false = refl

boolEq_sound : (a b : Bool) -> Eq (boolEq a b) true -> Eq a b
boolEq_sound true  true  e = refl
boolEq_sound true  false ()
boolEq_sound false true  ()
boolEq_sound false false e = refl

boolEq_false_eq : (a b : Bool) -> Eq (boolEq a b) false -> Eq a (boolNot b)
boolEq_false_eq true  true  ()
boolEq_false_eq true  false e = refl
boolEq_false_eq false true  e = refl
boolEq_false_eq false false ()

boolImp_false : (a b : Bool) -> Eq (boolImp a b) false -> Prod (Eq a true) (Eq b false)
boolImp_false true  true  ()
boolImp_false true  false e = prod refl refl
boolImp_false false b     ()

------------------------------------------------------------------------
-- Disjunction, read in both directions.
--
-- These four sat in LTL.Sets until LTL.Skel needed them: the tautology test of
-- (PC) is below Deriv, and Sets is far above it.

orTrue : (a b : Bool) -> Eq (boolOr a b) true -> Sum (Eq a true) (Eq b true)
orTrue true  b e = inl refl
orTrue false b e = inr e

orL : (a b : Bool) -> Eq a true -> Eq (boolOr a b) true
orL true  b e  = refl
orL false b ()

orR : (a b : Bool) -> Eq b true -> Eq (boolOr a b) true
orR true  b e = refl
orR false b e = e

tfAbs : Eq true false -> Empty
tfAbs ()

------------------------------------------------------------------------
-- Lists

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

infixr 8 _::_

append : {A : Set} -> List A -> List A -> List A
append []        ys = ys
append (x :: xs) ys = x :: append xs ys

length : {A : Set} -> List A -> Nat
length []        = zero
length (x :: xs) = suc (length xs)

map : {A B : Set} -> (A -> B) -> List A -> List B
map f []        = []
map f (x :: xs) = f x :: map f xs

-- filterCons takes the boolean as an explicit argument rather than using
-- "with", so that later proofs can case on it directly instead of having to
-- reproduce a with-abstraction.

filterCons : {A : Set} -> Bool -> A -> List A -> List A
filterCons true  x ys = x :: ys
filterCons false x ys = ys

filterL : {A : Set} -> (A -> Bool) -> List A -> List A
filterL p []        = []
filterL p (x :: xs) = filterCons (p x) x (filterL p xs)

anyL : {A : Set} -> (A -> Bool) -> List A -> Bool
anyL p []        = false
anyL p (x :: xs) = boolOr (p x) (anyL p xs)

nullB : {A : Set} -> List A -> Bool
nullB []        = true
nullB (x :: xs) = false

concatL : {A : Set} -> List (List A) -> List A
concatL []          = []
concatL (xs :: xss) = append xs (concatL xss)


------------------------------------------------------------------------
-- Membership

data Mem {A : Set} (x : A) : List A -> Set where
  memHd : {xs : List A}            -> Mem x (x :: xs)
  memTl : {y : A} {xs : List A} -> Mem x xs -> Mem x (y :: xs)

memAppL : {A : Set} {x : A} (xs ys : List A) -> Mem x xs -> Mem x (append xs ys)
memAppL []        ys ()
memAppL (z :: xs) ys memHd     = memHd
memAppL (z :: xs) ys (memTl h) = memTl (memAppL xs ys h)

memAppR : {A : Set} {x : A} (xs ys : List A) -> Mem x ys -> Mem x (append xs ys)
memAppR []        ys h = h
memAppR (z :: xs) ys h = memTl (memAppR xs ys h)

filterCons_mem : {A : Set} {x : A} (b : Bool) (y : A) (ys : List A)
              -> Mem x ys -> Mem x (filterCons b y ys)
filterCons_mem true  y ys h = memTl h
filterCons_mem false y ys h = h

filterCons_hd : {A : Set} (b : Bool) (y : A) (ys : List A)
             -> Eq b true -> Mem y (filterCons b y ys)
filterCons_hd true  y ys e = memHd
filterCons_hd false y ys ()

memMap : {A B : Set} (f : A -> B) {x : A} {xs : List A}
      -> Mem x xs -> Mem (f x) (map f xs)
memMap f memHd     = memHd
memMap f (memTl h) = memTl (memMap f h)

map_append : {A B : Set} (f : A -> B) (xs ys : List A)
          -> Eq (map f (append xs ys)) (append (map f xs) (map f ys))
map_append f []        ys = refl
map_append f (x :: xs) ys = eqCong (\ zs -> f x :: zs) (map_append f xs ys)

map_map : {A B C : Set} (f : B -> C) (g : A -> B) (xs : List A)
       -> Eq (map f (map g xs)) (map (\ x -> f (g x)) xs)
map_map f g []        = refl
map_map f g (x :: xs) = eqCong (\ zs -> f (g x) :: zs) (map_map f g xs)

memAppCase : {A : Set} {x : A} (xs ys : List A)
          -> Mem x (append xs ys) -> Sum (Mem x xs) (Mem x ys)
memAppCase []        ys h         = inr h
memAppCase (z :: xs) ys memHd     = inl memHd
memAppCase (z :: xs) ys (memTl h) =
  sumElim (\ k -> inl (memTl k)) (\ k -> inr k) (memAppCase xs ys h)

------------------------------------------------------------------------
-- The index / nth round-trip.
--
-- Every projection of a conjunct out of  chi v  goes through this pair, so it
-- is proved once, here, in both directions.

index : {A : Set} {x : A} {xs : List A} -> Mem x xs -> Nat
index memHd     = zero
index (memTl h) = suc (index h)

nth : {A : Set} -> List A -> Nat -> A -> A
nth []        n       d = d
nth (x :: xs) zero    d = x
nth (x :: xs) (suc n) d = nth xs n d

index_nth : {A : Set} {x : A} {xs : List A} (h : Mem x xs) (d : A)
         -> Eq (nth xs (index h) d) x
index_nth memHd     d = refl
index_nth (memTl h) d = index_nth h d

index_length : {A : Set} {x : A} {xs : List A} (h : Mem x xs)
            -> Lt (index h) (length xs)
index_length memHd     = ltZero
index_length (memTl h) = ltSuc (index_length h)

nth_mem : {A : Set} (xs : List A) (i : Nat) -> Lt i (length xs) -> (d : A)
       -> Mem (nth xs i d) xs
nth_mem []        i       ()        d
nth_mem (x :: xs) zero    lt        d = memHd
nth_mem (x :: xs) (suc i) (ltSuc l) d = memTl (nth_mem xs i l d)

ltSucCase : (i n : Nat) -> Lt i (suc n) -> Sum (Eq i n) (Lt i n)
ltSucCase zero    zero     lt        = inl refl
ltSucCase zero    (suc n)  lt        = inr ltZero
ltSucCase (suc j) zero     (ltSuc ())
ltSucCase (suc j) (suc n)  (ltSuc l) =
  sumElim (\ e -> inl (eqCong suc e)) (\ l' -> inr (ltSuc l')) (ltSucCase j n l)
