{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Trace -- G20 of FORMALISATION-PLAN.md: why each state was removed.
--
-- The elimination procedure of LTL.Elim drops a state by a single boolean,
-- keep P us v.  Theorem 4.1 proceeds by cases on the REASON, so the trace this
-- goal asks for is the inversion of that boolean into the two clauses of
-- Definition 3.1, carrying the witnesses each clause provides:
--
--   (R1)  v has no ->-successor in U_k;
--   (R2)  box A is a subformula of P, is pending at v, and v belongs to the
--         set W of LTL.Gfp -- equivalently, by gfpSound, the eventuality is
--         fulfilled at no state reachable from v inside U_k.
--
-- Recording the reason as a proof-carrying value rather than as a printed list
-- is what makes it usable in G21: byR2 hands over exactly the A, the
-- membership box A in Sub(P), and the two facts that case (R2) of the theorem
-- consumes.  A printed form is given at the end for observation.

module LTL.Trace where

open import LTL.Elim public

------------------------------------------------------------------------
-- The eventualities really are box-subformulas

boxArgs_mem : (As : List Formula) {A : Formula}
           -> Mem A (boxArgs As) -> Mem (box A) As
boxArgs_mem []              ()
boxArgs_mem (var n   :: As) m         = memTl (boxArgs_mem As m)
boxArgs_mem (neg B   :: As) m         = memTl (boxArgs_mem As m)
boxArgs_mem (imp B C :: As) m         = memTl (boxArgs_mem As m)
boxArgs_mem (nxt B   :: As) m         = memTl (boxArgs_mem As m)
boxArgs_mem (box B   :: As) memHd     = memHd
boxArgs_mem (box B   :: As) (memTl m) = memTl (boxArgs_mem As m)

------------------------------------------------------------------------
-- The reason a state is dropped

data Reason (P : Formula) (us : List Val) (v : Val) : Set where
  byR1 : Eq (r1 P us v) true -> Reason P us v
  byR2 : (A : Formula) -> Mem (box A) (sub P)
      -> Eq (valOf P v (box A)) false
      -> Mem v (gfpW P us A)
      -> Reason P us v

-- Inverting r2 now goes through evList_of: the disjunct that fired names a
-- PAIR, and evList_of says the pair is an eventuality of P together with its
-- own gfp set.  That is the only trace of the hoisting of LTL.Elim in the
-- proofs.

dropped : (P : Formula) (us : List Val) (v : Val)
       -> Eq (keep P us (evList P us) v) false -> Reason P us v
dropped P us v e =
  sumElim byR1 fromR2
          (orTrue (r1 P us v) (r2 P (evList P us) v)
                  (notFalse (boolOr (r1 P us v) (r2 P (evList P us) v)) e))
  where
    fromPair : (g : Ev) -> Mem g (evList P us) -> Eq (badEv P v g) true
            -> Reason P us v
    fromPair (prod A W) mg q =
      byR2 A (boxArgs_mem (sub P) (prodFst (evList_of P us mg)))
           (notTrue (valOf P v (box A)) (andTrueL (pending P v A) (memB v W) q))
           (eqSubst (\ Z -> Mem v Z) (prodSnd (evList_of P us mg))
                    (memB_sound v W (andTrueR (pending P v A) (memB v W) q)))

    fromSig : Sigma Ev (\ g -> Prod (Mem g (evList P us)) (Eq (badEv P v g) true))
           -> Reason P us v
    fromSig (sig g (prod m q)) = fromPair g m q

    fromR2 : Eq (r2 P (evList P us) v) true -> Reason P us v
    fromR2 e2 = fromSig (anyL_true (badEv P v) (evList P us) e2)

------------------------------------------------------------------------
-- The printed form.
--
-- One entry per state removed in the round, paired with the boolean r1: true
-- means the state went by (R1), false that (R1) did not fire and so (R2) did.

elimTrace : Formula -> List Val -> List (Prod Val Bool)
elimTrace P us =
  map (\ v -> prod v (r1 P us v))
      (filterL (\ v -> boolNot (keep P us (evList P us) v)) us)

reasons : Formula -> List Val -> List Bool
reasons P us = map prodSnd (elimTrace P us)

------------------------------------------------------------------------
-- Observation.
--
-- The observations are made on Ust, the demand-driven state set of G30, which
-- is what the procedure actually explores; St still has the six states of the
-- comment in LTL.Elim, but four of them are never reached from a state
-- containing neg benAri and the procedure never looks at them.
--
-- Only ONE state of neg benAri contains it, namely E, and E has no successor,
-- so the closure stops there and the single round removes it by (R1).  Ben-Ari's
-- own example therefore never exercises (R2) in this formulation.

trace_negBenAri : Eq (reasons negBenAri (Ust negBenAri)) (true :: [])
trace_negBenAri = refl

-- and the second round removes nothing, so the procedure has converged.

trace_negBenAri2 : Eq (reasons negBenAri (elimRound negBenAri (Ust negBenAri))) []
trace_negBenAri2 = refl

-- dia p loses no state at all.

trace_diaP : Eq (reasons diaP (Ust diaP)) []
trace_diaP = refl

------------------------------------------------------------------------
-- A small example that does exercise (R2).
--
--   bnb  =  box p -> box (nxt p)
--
-- is provable, and unlike benAri its refutation genuinely needs the loop
-- invariant.  The state with box p true and box (nxt p) false has successors,
-- so (R1) does not apply; but (T2) carries box p along every path, (S2) then
-- gives p and (T1) gives nxt p at every state reached, so the eventuality that
-- box (nxt p) leaves pending is fulfilled nowhere.  That is case (R2), and it
-- fires in the first round -- the false entry below.
--
-- The closure of the states containing neg bnb has just two members: box p and
-- neg (box (nxt p)) force p, and (T2) and (T3) carry both along every step, so
-- the only freedom left is the bit at nxt p.  The state with nxt p false has no
-- successor and goes by (R1) in the first round; the other one loops to itself,
-- and once its (R1)-victim is gone the eventuality that box (nxt p) leaves
-- pending is fulfilled at no reachable state, so it goes by (R2) in the second.
-- Nothing survives, and in particular no survivor contains neg bnb.
--
-- The (R2) round is the one that matters: extractR2 -- the loop invariant,
-- (Ind) and all -- is on the path from satB_negBnb to bnbProof in LTL.Extract.

bnb : Formula
bnb = imp (box (var zero)) (box (nxt (var zero)))

negBnb : Formula
negBnb = neg bnb

Ust_negBnb : Eq (length (Ust negBnb)) 2
Ust_negBnb = refl

trace_negBnb : Eq (reasons negBnb (Ust negBnb)) (true :: [])
trace_negBnb = refl

trace_negBnb2 : Eq (reasons negBnb (elimRound negBnb (Ust negBnb))) (false :: [])
trace_negBnb2 = refl

Uinf_negBnb : Eq (length (Uinf negBnb)) 0
Uinf_negBnb = refl

satB_negBnb : Eq (satB negBnb) false
satB_negBnb = refl

-- and the converse, which Hintikka's lemma needs: a box-subformula names an
-- eventuality.  That is boxArgs_of, and it followed boxArgs down to LTL.Skel
-- in Phase 9, where the (S2) premise of LTL.CompletePC needs it.
