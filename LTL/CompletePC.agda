{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.CompletePC -- G31 and G32 of FORMALISATION-PLAN.md: Lemma 2.6 again,
-- with the propositional bookkeeping discharged by (PC) instead of enumerated.
--
-- Nothing here replaces anything.  allComplete and stateComplete (LTL.Complete)
-- are untouched, and so are nonState, disjFilter and disjDrop, which is what
-- lets LTL.Proofs put the two certificates side by side: the point of the phase
-- is a COMPARISON, and it needs both proofs in the development.
--
-- What section 4g measured is that 97 % of a certificate is the case split over
-- the 2^|Sub P| valuations and the one-by-one refutation of the non-states.
-- Both are propositional, so Ben-Ari writes PC beside them (benari.pdf,
-- Definition 12.1, Axiom 0) and never writes them out.  With the eleventh
-- constructor of LTL.Deriv available they can be discharged the same way and,
-- unlike Ben-Ari's, CHECKED: pc takes Eq (isTaut A) true, a decidable condition
-- on A alone, with no substitution relation anywhere.
--
--   G31   allCompletePC As  = pc (tautAll As)            19263 -> 1
--   G32   stateCompletePC P = mpChain (boxArgs (sub P)) (pc (tautState P))
--
-- The chain is the |boxArgs (sub P)| instances of (T), one modus ponens each,
-- so G32 is  1 + 46 |boxArgs (sub P)|  constructors exactly: 1 for p -> p,
-- 47 for box p -> p where the old proof is 296839, and 277 for the
-- twenty-two-subformula example of section 4g, whose old proof cannot be
-- written down at all.  That is the shape the phase was after -- linear in the
-- number of eventualities where it was exponential in |Sub P|.
--
-- TWO DEPARTURES from the proposal in section 7, both simplifications, and both
-- measured in LTL.Proofs.
--
-- 1.  Section 7 gives G32 as  E P -> (D P -> beta P (St P))  with D P the full
--     disjunction, so that stateCompletePC would consume allCompletePC as well.
--     That premise is not needed.  The tautology is proved by BUILDING the
--     witness state out of the truth-table row -- skelVec of LTL.Taut, which is
--     a state as soon as (S2) holds -- rather than by SELECTING it from D P.
--     Carrying D P would cost nothing in the certificate, since allCompletePC
--     is one node, but it would put a formula of size 2^|Sub P| inside the side
--     condition, and the side condition is the one thing Phase 9 adds that a
--     machine may have to evaluate.  Without it the side condition is small
--     enough to check by refl, which LTL.Proofs does.  So G31 stands on its
--     own, as the pc form of the case split, and G32 does not go through it.
--
-- 2.  Section 7 makes E P a conjunction, assembled by (L2).  An implication
--     chain is cheaper by a factor of five per eventuality; see LTL.Taut.

module LTL.CompletePC where

open import LTL.Complete public
open import LTL.Taut     public

------------------------------------------------------------------------
-- G31: the case split.
--
-- allComplete As is the disjunction over all 2^|As| valuations, proved by
-- splitting on the members of As one at a time with (L6).  As a boolean it is
-- immediate: read the atoms by a, read each member of As by the skeleton, and
-- the row so obtained is one of the disjuncts and its literals are true by
-- construction.  allVecs_complete says the row is enumerated -- it has the
-- right length, by map_length -- and chiRowTrue that its chi holds.

splitFml : List Formula -> Formula
splitFml As = disj (map (chiOf As) (allVecs (length As)))

tautAll : (As : List Formula) -> Eq (isTaut (splitFml As)) true
tautAll As =
  allB_intro (\ a -> valFrom (atomsOf (splitFml As)) a (splitFml As))
             (allVecs (length (atomsOf (splitFml As))))
             row
  where
    Ats : List Formula
    Ats = atomsOf (splitFml As)

    row : {a : Val} -> Mem a (allVecs (length Ats))
       -> Eq (valFrom Ats a (splitFml As)) true
    row {a} m =
      disjTrue Ats a (map (chiOf As) (allVecs (length As)))
               (memMap (chiOf As)
                       (allVecs_complete (length As) (map (valFrom Ats a) As)
                                         (map_length (valFrom Ats a) As)))
               (chiRowTrue Ats a As)

allCompletePC : (As : List Formula)
             -> Deriv (disj (map (chiOf As) (allVecs (length As))))
allCompletePC As = pc (tautAll As)

------------------------------------------------------------------------
-- The (S2) premise.
--
-- E P of section 7:  box A -> A  for every box-subformula of P, as the premises
-- of an implication chain rather than as a conjunction -- see LTL.Taut for the
-- factor of five that costs.  Each premise is an instance of (T), boxElim of
-- LTL.Temporal, itself (Exp) followed by (L3); together they are the whole of
-- the new Lemma 2.6 beyond its single pc node.
--
-- It is needed because it is the one clause of Definition 2.2 that a
-- truth-table row does not satisfy for free: the skeleton reads box A and A as
-- two unrelated atoms, which is exactly why  box p -> p  is not a skeleton
-- tautology (LTL.Proofs, boxElim_not_taut).  (S1) and coherence, by contrast,
-- cost nothing at all -- see LTL.Taut.

s2List : Formula -> List Formula
s2List P = map s2Fml (boxArgs (sub P))

-- and the derivation half of LTL.Taut's boxChain: one modus ponens against one
-- instance of (T) per premise, left to right.  There is no s2Proof as a term of
-- its own -- the instances are consumed as they are met, which is what keeps
-- the count at 1 + 46 |boxArgs| with no propositional glue.

mpChain : (As : List Formula) {C : Formula}
       -> Deriv (impList (map s2Fml As) C) -> Deriv C
mpChain []        d = d
mpChain (A :: As) d = mpChain As (mp d boxElim)

------------------------------------------------------------------------
-- G32: Lemma 2.6.
--
-- The (S2) instances imply the state disjunction, propositionally.  Fix the
-- atom list of the implication itself and any row a of its truth table; the
-- premise says  box B -> B  holds under that reading for every box B in Sub P,
-- which is BoxOk, so skelVec is a state (LTL.Taut) and its chi is a true
-- disjunct of beta P (St P).
--
-- Note what does NOT happen.  No valuation is enumerated, no non-state is
-- refuted, and nothing is dropped from a disjunction: the row IS the state.
-- That is the same move G30 made computationally, where mkV builds a state
-- from an assignment to the atoms instead of filtering 2^|Sub P| vectors --
-- section 4g's closing remark, that the idea which made the search tractable is
-- the one that makes the certificate tractable, with the two now in one file.

stateFml : Formula -> Formula
stateFml P = impList (s2List P) (beta P (St P))

tautState : (P : Formula) -> Eq (isTaut (stateFml P)) true
tautState P =
  allB_intro (\ a -> valFrom (atomsOf (stateFml P)) a (stateFml P))
             (allVecs (length (atomsOf (stateFml P))))
             row
  where
    Ats : List Formula
    Ats = atomsOf (stateFml P)

    row : {a : Val} -> Mem a (allVecs (length Ats))
       -> Eq (valFrom Ats a (stateFml P)) true
    row {a} m =
      boxChain Ats a (boxArgs (sub P)) (beta P (St P))
               (\ g -> betaSkel Ats a P (\ B mb -> g B (boxArgs_of (sub P) mb)))

stateCompletePC : (P : Formula) -> Deriv (beta P (St P))
stateCompletePC P = mpChain (boxArgs (sub P)) (pc (tautState P))

------------------------------------------------------------------------
-- (L5) the same way, which is where the rest of the certificate is.
--
-- With Lemma 2.6 down to one node the dominant cost is disjElim: 426
-- constructors per disjunct, 1280 of the 1529 for box p -> p, growing with the
-- number of STATES.  It is propositional through and through -- the note proves
-- it from (P1)-(P3) alone -- so (PC) can take it whole:
--
--     (C1 -> C) -> ... -> (Cn -> C) -> ((C1 or ... or Cn) -> C)
--
-- is a tautology of its own skeleton, tautDisjElim, and the n branches are
-- discharged by n modus ponens.  So betaElimPC is  1 + n  nodes of glue where
-- betaElim is  17 + 426 n , and the certificate becomes linear in |St P| with a
-- constant of one.
--
-- mpVals walks the VALUATIONS rather than the disjuncts, so that no inversion
-- of  map (chi P)  is needed -- map_mem_inv lives in LTL.Bar, which LTL.Complete
-- cannot reach.  Same reason as mpChain above.

disjImpFml : List Formula -> Formula -> Formula
disjImpFml Cs C = impList (map (impTo C) Cs) (imp (disj Cs) C)

tautDisjElim : (Cs : List Formula) (C : Formula)
            -> Eq (isTaut (disjImpFml Cs C)) true
tautDisjElim Cs C =
  allB_intro (\ a -> valFrom (atomsOf (disjImpFml Cs C)) a (disjImpFml Cs C))
             (allVecs (length (atomsOf (disjImpFml Cs C))))
             row
  where
    Ats : List Formula
    Ats = atomsOf (disjImpFml Cs C)

    row : {a : Val} -> Mem a (allVecs (length Ats))
       -> Eq (valFrom Ats a (disjImpFml Cs C)) true
    row {a} m =
      impChain Ats a (map (impTo C) Cs) (imp (disj Cs) C)
               (\ g -> disjElimTrue Ats a Cs C (\ mD -> g (memMap (impTo C) mD)))

mpVals : (P : Formula) {C : Formula} (ws : List Val) {Z : Formula}
      -> ((w : Val) -> Mem w ws -> Deriv (imp (chi P w) C))
      -> Deriv (impList (map (impTo C) (map (chi P) ws)) Z) -> Deriv Z
mpVals P []        h d = d
mpVals P (w :: ws) h d =
  mpVals P ws (\ z m -> h z (memTl m)) (mp d (h w memHd))

betaElimPC : (P : Formula) {C : Formula} (ws : List Val)
          -> ((w : Val) -> Mem w ws -> Deriv (imp (chi P w) C))
          -> Deriv (imp (beta P ws) C)
betaElimPC P {C} ws h = mpVals P ws h (pc (tautDisjElim (map (chi P) ws) C))
