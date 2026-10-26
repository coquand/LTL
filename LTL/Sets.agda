{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Sets -- the list and set infrastructure the searches of Phases 5, 6 and
-- 8 run on.  It was the first half of LTL.Gfp until Phase 8; LTL.Bar has to sit
-- between the infrastructure and the greatest fixed point, since Bar needs
-- filterL and memB while the shrinking iteration of LTL.Gfp is now defined by
-- recursion on a Bar.
--
-- Le survives only inside barOfList, which is the bridge from a Kuratowski
-- finite list to an inductively finite predicate (LTL.Bar).  Nothing else in
-- the development counts any more.

module LTL.Sets where

open import LTL.Reach public

------------------------------------------------------------------------
-- Order on Nat.
--
-- Only needed to say that filterL shortens a list, which is what makes the
-- iteration below terminate.

data Le : Nat -> Nat -> Set where
  leZero : {n : Nat}             -> Le zero n
  leSuc  : {n m : Nat} -> Le n m -> Le (suc n) (suc m)

leRefl : (n : Nat) -> Le n n
leRefl zero    = leZero
leRefl (suc n) = leSuc (leRefl n)

leStep : {n m : Nat} -> Le n m -> Le n (suc m)
leStep leZero    = leZero
leStep (leSuc l) = leSuc (leStep l)

leTrans : {a b c : Nat} -> Le a b -> Le b c -> Le a c
leTrans leZero    l         = leZero
leTrans (leSuc k) (leSuc l) = leSuc (leTrans k l)

lePred : {a b : Nat} -> Le (suc a) (suc b) -> Le a b
lePred (leSuc l) = l

------------------------------------------------------------------------
-- Boolean glue

orFalseL : (a b : Bool) -> Eq (boolOr a b) false -> Eq a false
orFalseL true  b ()
orFalseL false b e = refl

orFalseR : (a b : Bool) -> Eq (boolOr a b) false -> Eq b false
orFalseR true  b ()
orFalseR false b e = e

notTrue : (b : Bool) -> Eq (boolNot b) true -> Eq b false
notTrue true  ()
notTrue false e = refl

notFalse : (b : Bool) -> Eq (boolNot b) false -> Eq b true
notFalse true  e = refl
notFalse false ()

impTrueB : (a b : Bool) -> Eq (boolImp a b) true -> Eq a true -> Eq b true
impTrueB true  b e q  = e
impTrueB false b e ()

impIntroB : (a b : Bool) -> (Eq a true -> Eq b true) -> Eq (boolImp a b) true
impIntroB true  b f = f refl
impIntroB false b f = refl

------------------------------------------------------------------------
-- Searching a list for a member that fails a boolean test.
--
-- This is the one case analysis the removing iteration performs: either some
-- state of W_i has a successor outside W_i, and the round removes it, or none
-- has and W_i is already closed.

data FindResult {A : Set} (p : A -> Bool) (xs : List A) : Set where
  found : (x : A) -> Mem x xs -> Eq (p x) false -> FindResult p xs
  allT  : ({x : A} -> Mem x xs -> Eq (p x) true)  -> FindResult p xs

emptyAll : {A : Set} (p : A -> Bool) {x : A} -> Mem x [] -> Eq (p x) true
emptyAll p ()

consAll : {A : Set} {p : A -> Bool} {y : A} {ys : List A}
       -> Eq (p y) true -> ({x : A} -> Mem x ys -> Eq (p x) true)
       -> {x : A} -> Mem x (y :: ys) -> Eq (p x) true
consAll e f memHd     = e
consAll e f (memTl m) = f m

findCons : {A : Set} {p : A -> Bool} {y : A} {ys : List A} (b : Bool)
        -> Eq (p y) b -> FindResult p ys -> FindResult p (y :: ys)
findCons true  e (found x m q) = found x (memTl m) q
findCons true  e (allT f)      = allT (consAll e f)
findCons false e r             = found _ memHd e

findFalse : {A : Set} (p : A -> Bool) (xs : List A) -> FindResult p xs
findFalse p []        = allT (emptyAll p)
findFalse p (y :: ys) = findCons (p y) refl (findFalse p ys)

------------------------------------------------------------------------
-- filterL against membership

filterCons_case : {A : Set} {x y : A} (b : Bool) (ys : List A)
               -> Mem x (filterCons b y ys) -> Sum (Eq x y) (Mem x ys)
filterCons_case true  ys memHd     = inl refl
filterCons_case true  ys (memTl m) = inr m
filterCons_case false ys m         = inr m

filter_sub : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
          -> Mem x (filterL p xs) -> Mem x xs
filter_sub p []        ()
filter_sub p (y :: ys) m =
  sumElim (\ e  -> eqSubst (\ z -> Mem z (y :: ys)) (eqSym e) memHd)
          (\ m' -> memTl (filter_sub p ys m'))
          (filterCons_case (p y) (filterL p ys) m)

filter_true : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
           -> Mem x xs -> Eq (p x) true -> Mem x (filterL p xs)
filter_true p []        ()        e
filter_true p (y :: ys) memHd     e = filterCons_hd (p y) y (filterL p ys) e
filter_true p (y :: ys) (memTl m) e =
  filterCons_mem (p y) y (filterL p ys) (filter_true p ys m e)

filterCons_prop : {A : Set} {p : A -> Bool} {x y : A} (b : Bool) -> Eq (p y) b
               -> (ys : List A) -> Mem x (filterCons b y ys)
               -> (Mem x ys -> Eq (p x) true) -> Eq (p x) true
filterCons_prop true  e ys memHd     k = e
filterCons_prop true  e ys (memTl m) k = k m
filterCons_prop false e ys m         k = k m

filter_prop : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
           -> Mem x (filterL p xs) -> Eq (p x) true
filter_prop p []        ()
filter_prop p (y :: ys) m =
  filterCons_prop (p y) refl (filterL p ys) m (filter_prop p ys)

------------------------------------------------------------------------
-- filterL against length.  This is the whole termination argument.

filterL_le : {A : Set} (p : A -> Bool) (xs : List A)
          -> Le (length (filterL p xs)) (length xs)
filterL_le p []        = leZero
filterL_le p (y :: ys) = aux (p y)
  where
    aux : (b : Bool)
       -> Le (length (filterCons b y (filterL p ys))) (suc (length ys))
    aux true  = leSuc  (filterL_le p ys)
    aux false = leStep (filterL_le p ys)

filterL_lt : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
          -> Mem x xs -> Eq (p x) false
          -> Le (suc (length (filterL p xs))) (length xs)
filterL_lt p []        ()        e
filterL_lt p (y :: ys) memHd     e =
  eqSubst (\ b -> Le (suc (length (filterCons b y (filterL p ys))))
                     (suc (length ys)))
          (eqSym e) (leSuc (filterL_le p ys))
filterL_lt p (y :: ys) (memTl m) e = aux (p y)
  where
    aux : (b : Bool)
       -> Le (suc (length (filterCons b y (filterL p ys)))) (suc (length ys))
    aux true  = leSuc  (filterL_lt p ys m e)
    aux false = leStep (filterL_lt p ys m e)

leZeroNil : {A : Set} (xs : List A) {x : A}
         -> Le (length xs) zero -> Mem x xs -> Empty
leZeroNil []        l  ()
leZeroNil (y :: ys) () m

nullB_mem : {A : Set} (xs : List A) {x : A}
         -> Eq (nullB xs) true -> Mem x xs -> Empty
nullB_mem []        e  ()
nullB_mem (y :: ys) () m

------------------------------------------------------------------------
-- anyL

anyL_true : {A : Set} (p : A -> Bool) (xs : List A) -> Eq (anyL p xs) true
         -> Sigma A (\ x -> Prod (Mem x xs) (Eq (p x) true))
anyL_true {A} p []        ()
anyL_true {A} p (y :: ys) e =
  sumElim (\ e1 -> sig y (prod memHd e1))
          (\ e2 -> shift (anyL_true p ys e2))
          (orTrue (p y) (anyL p ys) e)
  where
    shift : Sigma A (\ x -> Prod (Mem x ys) (Eq (p x) true))
         -> Sigma A (\ x -> Prod (Mem x (y :: ys)) (Eq (p x) true))
    shift (sig x (prod m q)) = sig x (prod (memTl m) q)

anyL_intro : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
          -> Mem x xs -> Eq (p x) true -> Eq (anyL p xs) true
anyL_intro p []        ()        e
anyL_intro p (y :: ys) memHd     e = orL (p y) (anyL p ys) e
anyL_intro p (y :: ys) (memTl m) e = orR (p y) (anyL p ys) (anyL_intro p ys m e)

anyL_false : {A : Set} (p : A -> Bool) (xs : List A) -> Eq (anyL p xs) false
          -> {x : A} -> Mem x xs -> Eq (p x) false
anyL_false p []        e  ()
anyL_false p (y :: ys) e memHd     = orFalseL (p y) (anyL p ys) e
anyL_false p (y :: ys) e (memTl m) =
  anyL_false p ys (orFalseR (p y) (anyL p ys) e) m

------------------------------------------------------------------------
-- allB

allB_false : {A : Set} (p : A -> Bool) (xs : List A) -> Eq (allB p xs) false
          -> Sigma A (\ x -> Prod (Mem x xs) (Eq (p x) false))
allB_false {A} p []        ()
allB_false {A} p (y :: ys) e =
  sumElim (\ e1 -> sig y (prod memHd e1))
          (\ e2 -> shift (allB_false p ys e2))
          (andFalse (p y) (allB p ys) e)
  where
    shift : Sigma A (\ x -> Prod (Mem x ys) (Eq (p x) false))
         -> Sigma A (\ x -> Prod (Mem x (y :: ys)) (Eq (p x) false))
    shift (sig x (prod m q)) = sig x (prod (memTl m) q)

nullB_false : {A : Set} (xs : List A) -> Eq (nullB xs) false
           -> Sigma A (\ x -> Mem x xs)
nullB_false []        ()
nullB_false (y :: ys) e = sig y memHd

------------------------------------------------------------------------
-- Reading a successor list

succsMem : (P : Formula) (us : List Val) (v : Val) {w : Val}
        -> Mem w (succs P us v) -> Prod (Mem w us) (Eq (step P v w) true)
succsMem P us v m =
  prod (filter_sub (step P v) us m) (filter_prop (step P v) us m)

succsIn : (P : Formula) (us : List Val) (v : Val) {w : Val}
       -> Mem w us -> Eq (step P v w) true -> Mem w (succs P us v)
succsIn P us v mw st = filter_true (step P v) us mw st

------------------------------------------------------------------------
-- Valuations as a set

eqCons : {b c : Bool} {v w : Val} -> Eq b c -> Eq v w -> Eq (b :: v) (c :: w)
eqCons refl refl = refl

valEq_sound : (v w : Val) -> Eq (valEq v w) true -> Eq v w
valEq_sound []       []       e = refl
valEq_sound []       (c :: w) ()
valEq_sound (b :: v) []       ()
valEq_sound (b :: v) (c :: w) e =
  eqCons (boolEq_sound b c (andTrueL (boolEq b c) (valEq v w) e))
         (valEq_sound v w (andTrueR (boolEq b c) (valEq v w) e))

memB_sound : (v : Val) (us : List Val) -> Eq (memB v us) true -> Mem v us
memB_sound v []        ()
memB_sound v (u :: us) e =
  sumElim (\ e1 -> eqSubst (\ z -> Mem v (z :: us)) (valEq_sound v u e1) memHd)
          (\ e2 -> memTl (memB_sound v us e2))
          (orTrue (valEq v u) (anyL (valEq v) us) e)

memB_complete : (v : Val) (us : List Val) -> Mem v us -> Eq (memB v us) true
memB_complete v []        ()
memB_complete v (u :: us) memHd     =
  orL (valEq v v) (anyL (valEq v) us) (valEq_refl v)
memB_complete v (u :: us) (memTl m) =
  orR (valEq v u) (anyL (valEq v) us) (memB_complete v us m)

memB_false : (v : Val) (us : List Val) -> Eq (memB v us) false -> Mem v us -> Empty
memB_false v us e m = tfAbs (eqTrans (eqSym (memB_complete v us m)) e)
