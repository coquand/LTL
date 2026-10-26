{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Val -- G4 of FORMALISATION-PLAN.md.
--
-- Valuations, the characteristic formula chi_v of Definition 2.4 of m4.tex, and
-- beta_U.  A valuation is a List Bool read against sub P positionally, so a
-- state is only a genuine function on the SET Sub(phi) once the duplicate
-- coherence clause of G5 is imposed (see FORMALISATION-PLAN.md section 0).
--
-- The empty disjunction is bot and the empty conjunction is top, which is the
-- convention fixed after Lemma 1.1 of the note; (L0) and (L5) then agree at
-- n = 0.

module LTL.Val where

open import LTL.Deriv public

------------------------------------------------------------------------
-- Valuations

------------------------------------------------------------------------
-- Signed occurrences, conjunction and disjunction over a list

lit : Formula -> Bool -> Formula
lit A true  = A
lit A false = neg A

conj : List Formula -> Formula
conj []        = top
conj (A :: As) = con A (conj As)

disj : List Formula -> Formula
disj []        = bot
disj (A :: As) = dis A (disj As)

------------------------------------------------------------------------
-- The characteristic formula

litList : List Formula -> Val -> List Formula
litList []        v          = []
litList (A :: As) []         = []
litList (A :: As) (b :: bs)  = lit A b :: litList As bs

chi : Formula -> Val -> Formula
chi P v = conj (litList (sub P) v)

beta : Formula -> List Val -> Formula
beta P vs = disj (map (chi P) vs)

------------------------------------------------------------------------
-- The projection lemma.
--
-- This is where the index/nth round-trip of G2 is paid off: a membership
-- proof for A in sub P locates the literal of A inside chi P v, signed by the
-- bit that v gives at that position.  Every conjunct projection of Phase 4
-- goes through it.

litList_mem : {A : Formula} (As : List Formula) (v : Val)
           -> Eq (length v) (length As)
           -> (h : Mem A As)
           -> Mem (lit A (bitAt v (index h))) (litList As v)
litList_mem []        v        e ()
litList_mem (A :: As) []       () h
litList_mem (A :: As) (b :: v) e memHd     = memHd
litList_mem (A :: As) (b :: v) e (memTl h) =
  memTl (litList_mem As v (sucInj e) h)

------------------------------------------------------------------------
-- Sanity checks by computation.
--
-- sub benAri has length 6 (LTL.Sub), so there are 2^6 = 64 valuations to
-- filter in G5.

allVecs_three : Eq (length (allVecs 3)) 8
allVecs_three = refl

allVecs_benAri : Eq (length (allVecs (length (sub benAri)))) 64
allVecs_benAri = refl

-- Positions 1 and 4 of sub benAri are the same formula (box p), so a valuation
-- disagreeing there yields a chi containing both box p and neg (box p).  This
-- is exactly what the coherence clause of G5 will exclude.

badVal : Val
badVal = true :: true :: true :: true :: false :: true :: []

badVal_length : Eq (length badVal) (length (sub benAri))
badVal_length = refl
