{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Formula -- G1 of FORMALISATION-PLAN.md.
--
-- The language of m4.tex section 1: formulas built from propositional
-- variables by neg, imp, nxt (the next operator) and box.  Conjunction,
-- disjunction, equivalence, the eventually operator and bot are abbreviations,
-- exactly as in the note.
--
-- formEq is decidable equality.  It is used by the duplicate-coherence clause
-- of isState (G5), by lookup (G4), and by the pigeonhole of G23, so it is
-- proved sound and complete here once and for all.

module LTL.Formula where

open import LTL.Prelude public

------------------------------------------------------------------------
-- Formulas

data Formula : Set where
  var : Nat -> Formula
  neg : Formula -> Formula
  imp : Formula -> Formula -> Formula
  nxt : Formula -> Formula
  box : Formula -> Formula

------------------------------------------------------------------------
-- Abbreviations (m4.tex section 1)

top : Formula
top = imp (var zero) (var zero)

bot : Formula
bot = neg top

dis : Formula -> Formula -> Formula
dis A B = imp (neg A) B

con : Formula -> Formula -> Formula
con A B = neg (imp A (neg B))

iff : Formula -> Formula -> Formula
iff A B = con (imp A B) (imp B A)

dia : Formula -> Formula
dia A = neg (box (neg A))

------------------------------------------------------------------------
-- Decidable equality.
--
-- All twenty-five cases are written out: --exact-split rejects a catch-all
-- clause overlapping the diagonal ones.

formEq : Formula -> Formula -> Bool
formEq (var n)   (var m)   = natEq n m
formEq (var n)   (neg B)   = false
formEq (var n)   (imp B C) = false
formEq (var n)   (nxt B)   = false
formEq (var n)   (box B)   = false

formEq (neg A)   (var m)   = false
formEq (neg A)   (neg B)   = formEq A B
formEq (neg A)   (imp B C) = false
formEq (neg A)   (nxt B)   = false
formEq (neg A)   (box B)   = false

formEq (imp A A') (var m)   = false
formEq (imp A A') (neg B)   = false
formEq (imp A A') (imp B C) = boolAnd (formEq A B) (formEq A' C)
formEq (imp A A') (nxt B)   = false
formEq (imp A A') (box B)   = false

formEq (nxt A)   (var m)   = false
formEq (nxt A)   (neg B)   = false
formEq (nxt A)   (imp B C) = false
formEq (nxt A)   (nxt B)   = formEq A B
formEq (nxt A)   (box B)   = false

formEq (box A)   (var m)   = false
formEq (box A)   (neg B)   = false
formEq (box A)   (imp B C) = false
formEq (box A)   (nxt B)   = false
formEq (box A)   (box B)   = formEq A B

------------------------------------------------------------------------
-- formEq is reflexive, hence complete

formEq_refl : (A : Formula) -> Eq (formEq A A) true
formEq_refl (var n)   = natEq_refl n
formEq_refl (neg A)   = formEq_refl A
formEq_refl (imp A B) = andIntro (formEq A A) (formEq B B)
                                 (formEq_refl A) (formEq_refl B)
formEq_refl (nxt A)   = formEq_refl A
formEq_refl (box A)   = formEq_refl A

formEq_complete : (A B : Formula) -> Eq A B -> Eq (formEq A B) true
formEq_complete A B refl = formEq_refl A

------------------------------------------------------------------------
-- formEq is sound

formEq_sound : (A B : Formula) -> Eq (formEq A B) true -> Eq A B
formEq_sound (var n)   (var m)   p = eqCong var (natEq_sound n m p)
formEq_sound (var n)   (neg B)   ()
formEq_sound (var n)   (imp B C) ()
formEq_sound (var n)   (nxt B)   ()
formEq_sound (var n)   (box B)   ()

formEq_sound (neg A)   (var m)   ()
formEq_sound (neg A)   (neg B)   p = eqCong neg (formEq_sound A B p)
formEq_sound (neg A)   (imp B C) ()
formEq_sound (neg A)   (nxt B)   ()
formEq_sound (neg A)   (box B)   ()

formEq_sound (imp A A') (var m)   ()
formEq_sound (imp A A') (neg B)   ()
formEq_sound (imp A A') (imp B C) p =
  impCong (formEq_sound A B (andTrueL (formEq A B) (formEq A' C) p))
          (formEq_sound A' C (andTrueR (formEq A B) (formEq A' C) p))
  where
    impCong : {X Y X' Y' : Formula} -> Eq X Y -> Eq X' Y' -> Eq (imp X X') (imp Y Y')
    impCong refl refl = refl
formEq_sound (imp A A') (nxt B)   ()
formEq_sound (imp A A') (box B)   ()

formEq_sound (nxt A)   (var m)   ()
formEq_sound (nxt A)   (neg B)   ()
formEq_sound (nxt A)   (imp B C) ()
formEq_sound (nxt A)   (nxt B)   p = eqCong nxt (formEq_sound A B p)
formEq_sound (nxt A)   (box B)   ()

formEq_sound (box A)   (var m)   ()
formEq_sound (box A)   (neg B)   ()
formEq_sound (box A)   (imp B C) ()
formEq_sound (box A)   (nxt B)   ()
formEq_sound (box A)   (box B)   p = eqCong box (formEq_sound A B p)
