{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Deriv -- G3 of FORMALISATION-PLAN.md.
--
-- The system L of m4.tex section 1, as a plain inductive family: the eight
-- axiom schemes together with modus ponens and generalisation.  Replacing
-- Ben-Ari's (PC) by (P1)-(P3) is what makes that possible: no tautology checker
-- and no substitution relation are needed to say what a derivation is.
--
-- Phase 8 adds (PC) back as an ELEVENTH constructor, with a decidable side
-- condition on the formula itself and no substitution relation -- see below and
-- LTL.Skel.  Nothing in Phases 1-7 uses it, so the ten-constructor system is
-- still what every lemma of this development is proved in; pc is there because
-- it is what makes a certificate short, and LTL.Proofs measures the difference.

module LTL.Deriv where

open import LTL.Skel public

data Deriv : Formula -> Set where

  -- (P1)  A -> (B -> A)
  p1 : {A B : Formula}
    -> Deriv (imp A (imp B A))

  -- (P2)  (A -> (B -> C)) -> ((A -> B) -> (A -> C))
  p2 : {A B C : Formula}
    -> Deriv (imp (imp A (imp B C)) (imp (imp A B) (imp A C)))

  -- (P3)  (neg B -> neg A) -> (A -> B)
  p3 : {A B : Formula}
    -> Deriv (imp (imp (neg B) (neg A)) (imp A B))

  -- (K box)  box (A -> B) -> (box A -> box B)
  kbox : {A B : Formula}
      -> Deriv (imp (box (imp A B)) (imp (box A) (box B)))

  -- (K nxt)  nxt (A -> B) -> (nxt A -> nxt B)
  knxt : {A B : Formula}
      -> Deriv (imp (nxt (imp A B)) (imp (nxt A) (nxt B)))

  -- (Exp)  box A -> (A and nxt A and nxt (box A))
  exp : {A : Formula}
     -> Deriv (imp (box A) (con A (con (nxt A) (nxt (box A)))))

  -- (Ind)  box (A -> nxt A) -> (A -> box A)
  ind : {A : Formula}
     -> Deriv (imp (box (imp A (nxt A))) (imp A (box A)))

  -- (Lin)  nxt (neg A) <-> neg (nxt A)
  lin : {A : Formula}
     -> Deriv (iff (nxt (neg A)) (neg (nxt A)))

  -- (PC)  Ben-Ari's Axiom 0, without the substitution relation.
  --
  -- Definition 12.1 of benari.pdf takes "any substitution instance of a valid
  -- propositional formula".  m4.tex Remark 6.4 rejects that because it needs a
  -- tautology checker AND a substitution relation to say what a derivation is,
  -- and then a substitution lemma for soundness.  Only the first half is
  -- unavoidable: asking that A be a tautology OF ITS OWN SKELETON -- its var,
  -- nxt and box subformulas taken as atoms -- picks out the same formulas, is a
  -- decidable condition on A alone, and keeps Deriv a plain inductive family.
  -- isTaut is that test (LTL.Skel), and soundness is tautSound.
  --
  -- Nothing in Phases 1-8 uses it: (L0)-(L7) and everything above them are
  -- derived from (P1)-(P3) exactly as before, so the eleventh constructor is
  -- additive.  What it buys is the length of a certificate; see LTL.Proofs.
  pc : {A : Formula} -> Eq (isTaut A) true -> Deriv A

  -- modus ponens
  mp : {A B : Formula}
    -> Deriv (imp A B) -> Deriv A -> Deriv B

  -- generalisation
  gen : {A : Formula}
     -> Deriv A -> Deriv (box A)
