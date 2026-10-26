{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Reach -- G7 of FORMALISATION-PLAN.md.
--
-- Reach_U(v) of m4.tex section 3: the states reachable from v by ->-steps
-- inside U, v included.  It is needed twice: in condition (R2) of
-- Definition 3.1, and to build the loop invariant B = beta_W of Theorem 4.1,
-- where W = Reach_{U_k}(v).
--
-- Computed by fuel-bounded iteration rather than well-founded recursion: each
-- round either adds a state or stabilises, so length us rounds suffice.
--
-- What survives of this module is the SET machinery -- valEq, memB, insertV,
-- unionV -- which the rest of the development uses throughout.  reach itself is
-- kept for the computation below, but the elimination procedure does not use
-- it: "length us rounds suffice" is exactly the claim one has to prove to get
-- the closure property of Theorem 4.1 step (ii) out of it, and it is a
-- pigeonhole argument over a duplicate-free accumulator.  LTL.Gfp replaces the
-- reachable set by the largest closed set of unfulfilling states, where closure
-- is free, and shows in gfpSound/gfpComplete that the resulting condition (R2)
-- is the note's, with Reach_U(v) taken in its exact sense rather than
-- approximated from below by a fuel bound.

module LTL.Reach where

open import LTL.Step public

------------------------------------------------------------------------
-- Valuations as a set

valEq : Val -> Val -> Bool
valEq []       []       = true
valEq []       (c :: w) = false
valEq (b :: v) []       = false
valEq (b :: v) (c :: w) = boolAnd (boolEq b c) (valEq v w)

valEq_refl : (v : Val) -> Eq (valEq v v) true
valEq_refl []           = refl
valEq_refl (true  :: v) = valEq_refl v
valEq_refl (false :: v) = valEq_refl v

memB : Val -> List Val -> Bool
memB v us = anyL (valEq v) us

insertV : Val -> List Val -> List Val
insertV v us = filterCons (boolNot (memB v us)) v us

unionV : List Val -> List Val -> List Val
unionV []        ys = ys
unionV (x :: xs) ys = insertV x (unionV xs ys)

------------------------------------------------------------------------
-- One round of expansion, then the fuel-bounded closure

reachStep : Formula -> List Val -> List Val -> List Val
reachStep P us acc = unionV (concatL (map (succs P us) acc)) acc

reachIter : Formula -> Nat -> List Val -> List Val -> List Val
reachIter P zero    us acc = acc
reachIter P (suc n) us acc = reachIter P n us (reachStep P us acc)

reach : Formula -> List Val -> Val -> List Val
reach P us v = reachIter P (length us) us (v :: [])

------------------------------------------------------------------------
-- Computational checks.
--
-- For dia p the three states are s_a = 1010, s_b = 1001, s_c = 0110 (see
-- LTL.Step).  s_a and s_b reach everything; s_c is a sink, reaching only
-- itself.

reach_diaP : Eq (map (\ v -> length (reach diaP (St diaP) v)) (St diaP))
                (3 :: 3 :: 1 :: [])
reach_diaP = refl
