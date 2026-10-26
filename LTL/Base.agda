{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Base  (verbatim copy of BRA3.Base, module renamed) -- basic ASCII prelude (Nat, Bool, Eq).
--
-- Self-contained; no dependency on BRA2.

module LTL.Base where

------------------------------------------------------------------------
-- Natural numbers

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

------------------------------------------------------------------------
-- Bool

data Bool : Set where
  true  : Bool
  false : Bool

boolCase : {A : Set} -> Bool -> A -> A -> A
boolCase true  x _ = x
boolCase false _ y = y

natEq : Nat -> Nat -> Bool
natEq zero    zero    = true
natEq zero    (suc _) = false
natEq (suc _) zero    = false
natEq (suc n) (suc m) = natEq n m

------------------------------------------------------------------------
-- Empty and Unit

data Empty : Set where

emptyElim : {A : Set} -> Empty -> A
emptyElim ()

record Unit : Set where
  constructor tt

------------------------------------------------------------------------
-- Propositional equality

data Eq {A : Set} (x : A) : A -> Set where
  refl : Eq x x

eqSym : {A : Set} {x y : A} -> Eq x y -> Eq y x
eqSym refl = refl

eqTrans : {A : Set} {x y z : A} -> Eq x y -> Eq y z -> Eq x z
eqTrans refl q = q

eqCong : {A B : Set} (f : A -> B) {x y : A} -> Eq x y -> Eq (f x) (f y)
eqCong f refl = refl

eqSubst : {A : Set} (P : A -> Set) {x y : A} -> Eq x y -> P x -> P y
eqSubst P refl px = px
