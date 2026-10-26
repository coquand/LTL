{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Elim -- G8 of FORMALISATION-PLAN.md.
--
-- Definition 3.1 of m4.tex.  Starting from U_0 = St(P), remove every state to
-- which one of the following applies, and repeat:
--
--   (R1)  v has no ->-successor in U_k;
--   (R2)  for some j, the j-th eventuality is pending at v and is fulfilled at
--         no state of Reach_{U_k}(v).
--
-- The eventualities are indexed by the box-subformulas of P: box A is pending
-- at v when box A is not in v, and fulfilled at w when A is not in w.
--
-- (R2) is stated through gfpW of LTL.Gfp rather than through reach: "the j-th
-- eventuality is fulfilled at no state of Reach_{U_k}(v)" is written "v belongs
-- to the largest ->-closed set of states of U_k at which A_j still holds".
-- gfpSound and gfpComplete of LTL.Gfp show the two are the same condition, with
-- Reach taken in its exact sense (the inductive type Path of ->-paths inside
-- U_k).  The reason for the change is Theorem 4.1: its case (R2) needs the set
-- to be closed under successors, and for a greatest fixed point that is free,
-- where for the reachable set it is a pigeonhole argument.
--
-- Two things are new in Phase 8, and both are G29.
--
-- The iteration stops when a round removes nothing, by recursion on a Bar,
-- instead of being run  length (St P)  times and shown afterwards to have
-- reached a fixed point.  There is no fuel and no Le measure here at all.
--
-- The gfp sets are computed ONCE PER ROUND rather than once per state.  W_j
-- does not depend on the state being tested, but written as  memB v (gfpW P us
-- A)  under the binder for v it was rebuilt for every pending state of the
-- round, which is where most of the 34.6 s of checkpoint C5 was going.  evList
-- pairs each eventuality with its set, the pair list is the argument the round
-- filters against, and badEv reads the set out of the pair.  Laziness keeps the
-- cost down further: the set in a pair is forced only if the eventuality is
-- actually pending at the state being tested.

module LTL.Elim where

open import LTL.Gfp public

------------------------------------------------------------------------
-- The eventualities.
--
-- boxArgs -- the A for which box A occurs in sub P -- was defined here until
-- Phase 9 moved it to LTL.Skel, which is below Deriv and so reachable from
-- LTL.Complete as well; see the comment there.

------------------------------------------------------------------------
-- (R1)

r1 : Formula -> List Val -> Val -> Bool
r1 P us v = nullB (succs P us v)

pending : Formula -> Val -> Formula -> Bool
pending P v A = boolNot (valOf P v (box A))

------------------------------------------------------------------------
-- (R2), with the sets hoisted out of the state loop

Ev : Set
Ev = Prod Formula (List Val)

evList : Formula -> List Val -> List Ev
evList P us = map (\ A -> prod A (gfpW P us A)) (boxArgs (sub P))

evList_mem : (P : Formula) (us : List Val) {A : Formula}
          -> Mem A (boxArgs (sub P)) -> Mem (prod A (gfpW P us A)) (evList P us)
evList_mem P us m = memMap (\ A -> prod A (gfpW P us A)) m

evList_of : (P : Formula) (us : List Val) {A : Formula} {W : List Val}
         -> Mem (prod A W) (evList P us)
         -> Prod (Mem A (boxArgs (sub P))) (Eq W (gfpW P us A))
evList_of P us {A} {W} m =
  fromSig (map_mem_inv (\ B -> prod B (gfpW P us B)) (boxArgs (sub P)) m)
  where
    fromSig : Sigma Formula
                (\ B -> Prod (Mem B (boxArgs (sub P)))
                             (Eq (prod A W) (prod B (gfpW P us B))))
           -> Prod (Mem A (boxArgs (sub P))) (Eq W (gfpW P us A))
    fromSig (sig B (prod mB e)) =
      eqSubst (\ C -> Prod (Mem C (boxArgs (sub P))) (Eq W (gfpW P us C)))
              (eqSym (eqCong prodFst e))
              (prod mB (eqCong prodSnd e))

badEv : Formula -> Val -> Ev -> Bool
badEv P v (prod A W) = boolAnd (pending P v A) (memB v W)

r2 : Formula -> List Ev -> Val -> Bool
r2 P gs v = anyL (badEv P v) gs

------------------------------------------------------------------------
-- One round

keep : Formula -> List Val -> List Ev -> Val -> Bool
keep P us gs v = boolNot (boolOr (r1 P us v) (r2 P gs v))

elimRound : Formula -> List Val -> List Val
elimRound P us = filterL (keep P us (evList P us)) us

------------------------------------------------------------------------
-- The elimination, run until a round removes nothing.
--
-- findFalse asks whether any state of us fails keep.  If none does, us is the
-- answer: that is Definition 3.1's stopping condition, read directly rather
-- than recovered from a fixed-point equation.  If one does, it is dropped from
-- the Bar's predicate along with the round, which is what makes the recursive
-- call structurally smaller.

elimGo   : (P : Formula) {E : Val -> Bool} (us : List Val)
        -> InE E us -> IFin E -> List Val
elimFind : (P : Formula) {E : Val -> Bool} (us : List Val)
        -> InE E us -> IFin E
        -> FindResult (keep P us (evList P us)) us -> List Val

elimGo P us sb bar =
  elimFind P us sb bar (findFalse (keep P us (evList P us)) us)

elimFind P us sb bar      (allT f)      = us
elimFind P us sb (cBar h) (found x m q) =
  elimGo P (elimRound P us)
         (dropInE (keep P us (evList P us)) us sb x q) (h x (sb x m))

------------------------------------------------------------------------
-- U_infinity.
--
-- The elimination starts from Ust P, the set LTL.Closure gives the search, not
-- from the complete state list St P, which is left to the derivations (G30).
-- Its Bar is guardedVecBar: the states have length |sub P|, and the vectors of
-- a given length are inductively finite by induction on the length, so nothing
-- here needs the enumeration allVecs -- nor even  length (Ust P) , which the
-- fuel of the old elimIter forced.  guardBar (siles.pdf section 5) is what
-- keeps the finiteness proof from being forced as the search runs.

Uinf : Formula -> List Val
Uinf P = elimGo P (Ust P) (ustInE P) (ustBar P)

removed : Formula -> List Val
removed P = filterL (\ v -> boolNot (memB v (Uinf P))) (Ust P)

------------------------------------------------------------------------
-- The decision, as a boolean.
--
-- This is the test of Theorem 6.1: is there a surviving state in which the
-- input formula holds?  Run on neg P, "no" means P is provable.

satB : Formula -> Bool
satB P = anyL (\ v -> valOf P v P) (Uinf P)

------------------------------------------------------------------------
-- Checkpoint C1.
--
-- dia p is satisfiable: all three states survive, and one of them makes
-- dia p true.

Uinf_diaP : Eq (length (Uinf diaP)) 3
Uinf_diaP = refl

satB_diaP : Eq (satB diaP) true
satB_diaP = refl

-- neg benAri is unsatisfiable, so box p -> nxt (box p) is provable.
--
-- Of the six states, E and D are removed in the first round by (R1) alone --
-- neither has a successor -- and E is the only state containing neg benAri.
-- Ben-Ari's own worked example therefore never reaches (R2) in this
-- formulation: (T2) makes  box p  together with  neg (nxt (box p))  contradict
-- in a single step, where his tableau needed the loop invariant because it
-- carried  nxt (box p)  as an explicit member of the closure.

Uinf_negBenAri : Eq (length (Uinf negBenAri)) 0
Uinf_negBenAri = refl

removed_negBenAri : Eq (length (removed negBenAri)) 1
removed_negBenAri = refl

satB_negBenAri : Eq (satB negBenAri) false
satB_negBenAri = refl

------------------------------------------------------------------------
-- An example that does exercise (R2), recorded but not checked here.
--
-- Since benAri is settled by (R1) alone, it is not an adequate end-to-end test
-- of the extraction theorem.  The induction axiom is:
--
--   indAx  = imp (box (imp p (nxt p))) (imp p (box p))
--
-- Running the procedure on  neg indAx  gives, measured:
--
--   length (sub negInd)   = 11        (so 2048 valuations to filter)
--   length (St negInd)    = 10
--   length (Uinf negInd)  =  7
--   satB negInd           = false     -- hence  indAx  is provable
--   (R1) fires on 1 state of U_0, (R2) fires on 1 state of U_0
--
-- So (R2) does fire, and the loop-invariant branch of Theorem 4.1 is genuinely
-- reached.  A smaller example with the same property is bnb in LTL.Trace, and
-- that is the one checkpoint C4 uses.
