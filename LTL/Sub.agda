{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Sub -- G2 of FORMALISATION-PLAN.md.
--
-- Sub(phi) of m4.tex section 2: a plain structural recursion, no closure
-- operation (see Remark 2.1 of the note).
--
-- The six membership lemmas the development needs are all consequences of a
-- single transitivity lemma sub_mono together with sub_self, so they are
-- two-liners rather than six separate inductions.

module LTL.Sub where

open import LTL.Formula public

------------------------------------------------------------------------
-- Subformulas

sub : Formula -> List Formula
sub (var n)   = var n :: []
sub (neg A)   = neg A :: sub A
sub (imp A B) = imp A B :: append (sub A) (sub B)
sub (nxt A)   = nxt A :: sub A
sub (box A)   = box A :: sub A

------------------------------------------------------------------------
-- sub P always begins with P

sub_self : (A : Formula) -> Mem A (sub A)
sub_self (var n)   = memHd
sub_self (neg A)   = memHd
sub_self (imp A B) = memHd
sub_self (nxt A)   = memHd
sub_self (box A)   = memHd

------------------------------------------------------------------------
-- Transitivity: sub is closed under passing to subformulas of its members.
--
-- The memHd cases are all  k  itself, since there Q is P.

sub_mono : (P : Formula) {Q : Formula} -> Mem Q (sub P)
        -> {X : Formula} -> Mem X (sub Q) -> Mem X (sub P)
sub_mono (var n)   memHd      k = k
sub_mono (var n)   (memTl ()) k
sub_mono (neg A)   memHd      k = k
sub_mono (neg A)   (memTl h)  k = memTl (sub_mono A h k)
sub_mono (imp A B) memHd      k = k
sub_mono (imp A B) (memTl h)  k =
  memTl (sumElim (\ h1 -> memAppL (sub A) (sub B) (sub_mono A h1 k))
                 (\ h2 -> memAppR (sub A) (sub B) (sub_mono B h2 k))
                 (memAppCase (sub A) (sub B) h))
sub_mono (nxt A)   memHd      k = k
sub_mono (nxt A)   (memTl h)  k = memTl (sub_mono A h k)
sub_mono (box A)   memHd      k = k
sub_mono (box A)   (memTl h)  k = memTl (sub_mono A h k)

------------------------------------------------------------------------
-- The six membership lemmas

sub_neg : (P : Formula) {A : Formula} -> Mem (neg A) (sub P) -> Mem A (sub P)
sub_neg P {A} h = sub_mono P h (memTl (sub_self A))

sub_impL : (P : Formula) {A B : Formula} -> Mem (imp A B) (sub P) -> Mem A (sub P)
sub_impL P {A} {B} h = sub_mono P h (memTl (memAppL (sub A) (sub B) (sub_self A)))

sub_impR : (P : Formula) {A B : Formula} -> Mem (imp A B) (sub P) -> Mem B (sub P)
sub_impR P {A} {B} h = sub_mono P h (memTl (memAppR (sub A) (sub B) (sub_self B)))

sub_nxt : (P : Formula) {A : Formula} -> Mem (nxt A) (sub P) -> Mem A (sub P)
sub_nxt P {A} h = sub_mono P h (memTl (sub_self A))

sub_box : (P : Formula) {A : Formula} -> Mem (box A) (sub P) -> Mem A (sub P)
sub_box P {A} h = sub_mono P h (memTl (sub_self A))

------------------------------------------------------------------------
-- sub produces duplicates.
--
-- This is the point recorded in FORMALISATION-PLAN.md section 0.  Ben-Ari's own
-- example is already an instance: for  box p -> nxt (box p)  we get
--
--   [ imp (box p) (nxt (box p)) , box p , p , nxt (box p) , box p , p ]
--
-- of length 6, with  box p  and  p  each occurring twice.  A valuation as a
-- List Bool of length 6 therefore assigns them independent bits, which is why
-- isState (G5) carries a duplicate-coherence clause.

benAri : Formula
benAri = imp (box (var zero)) (nxt (box (var zero)))

subBenAri_length : Eq (length (sub benAri)) 6
subBenAri_length = refl

subBenAri_dup : Eq (nth (sub benAri) 1 bot) (nth (sub benAri) 4 bot)
subBenAri_dup = refl
