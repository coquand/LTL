{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Lecture -- lecture15.pdf's own worked example, run through decide.
--
-- The appendix of lecture15.pdf (pages 139-141) analyses
--
--     F a and F b  ->  F (a and b)
--
-- by hand: it lists Sub, the locally consistent states with F(a and b) = 0,
-- their outgoing edges, and a countermodel path.  The formula is not valid, so
-- decide takes the countermodel branch, and everything the lecture computes can
-- be checked against what the development computes.
--
-- THE GRAPH IS THE SAME.  Writing a state as  8a + 4b + 2 Fa + Fb , the
-- lecture's s0..s7 are 0, 1, 2, 3, 5, 7, 10, 11, and Ust of the negation is
-- exactly that set of eight, with the same twenty-four edges and the same
-- out-degrees, enumerated in a different order.  That is worth checking because
-- the two constructions have almost nothing in common: the lecture ASSUMES
-- F(a and b) = 0 to cut its table down to eight rows, while here the eight are
-- the closure under successors of the states containing the negation, and
-- F(a and b) = 0 falls out because the negation forces it and the closure
-- propagates it.  Before that, StC has seventeen locally consistent states,
-- built from 32 candidates over 5 atoms, where the lecture would filter 2^6
-- valuations of its Sub.
--
-- THE COUNTERMODEL IS NOT.  The lecture gives
--
--     s3 -> s5 -> s7 -> s7 -> ...          (loop at s7)
--
-- and that path is NOT FAIR.  At s7 one has Fb = 1 and b = 0, so s7 is outside
-- the fairness set  F_Fb = { v | v (Fb) = 0 or v (b) = 1 } : looping there
-- forever promises b and never delivers it, which is the very situation the
-- fairness condition exists to exclude, and is the same shape as the lecture's
-- own Example 2.  The path it presumably meant is  s3 -> s5 -> s7 -> s5 -> ... ,
-- alternating so that b recurs at s5 and a at s7; both edges exist.
--
-- decide returns a different and shorter one,
--
--     s7 -> s4 -> s0 -> s0 -> ...          (loop at s0)
--
-- a at stage 0, b at stage 1, and everything false from stage 2 on: Fa and Fb
-- are both fulfilled at once and a and b are never true together.  It ends in
-- s0, a state where nothing is pending at all, which the hand analysis never
-- considers because it is looking for a loop that KEEPS the eventualities
-- alive.
--
-- The last three lines are the point, and they are the fairness predicate of
-- LTL.SccLasso applied to the two ends of the run.  For the eventuality
-- F b -- which in the box-only syntax is  neg (box (neg b)) , so the argument
-- of the box is  neg b  --
--
--     evPred R (neg b) s7 = false          s7 is outside F_Fb : the lecture's
--                                          loop cannot be fair
--     evPred R (neg b) s0 = true           the loop decide returns can be
--     evPred R (neg a) s7 = true           and s7 is inside F_Fa, exactly as
--                                          the lecture says (a holds there)
--
-- so the objection is not a matter of reading: it is a checked equation about
-- the lecture's own state, against the lecture's own fairness set.

module LTL.Lecture where

open import LTL.DecideSCC public

------------------------------------------------------------------------
-- The formula, in the box-only syntax of m4.tex.

pa : Formula
pa = var zero

pb : Formula
pb = var (suc zero)

fab : Formula
fab = imp (con (dia pa) (dia pb)) (dia (con pa pb))

R : Formula
R = neg fab

------------------------------------------------------------------------
-- The state space.
--
-- 21 positions of Sub, but only 5 atoms -- a, b and the three boxes behind the
-- three F's -- so 32 candidates are built and 17 are states.  The lecture's
-- table is the closure, which is 8.

lec_sizes : Eq (length (sub R) :: length (atoms (sub R)) :: length (cands R)
             :: length (StC R) :: length (Ust R) :: length (Uinf R)
             :: length (boxArgs (sub R)) :: [])
               (21 :: 5 :: 32 :: 17 :: 8 :: 8 :: 3 :: [])
lec_sizes = refl

------------------------------------------------------------------------
-- The eight states, in the lecture's own encoding.

bitV : Bool -> Nat -> Nat
bitV true  n = n
bitV false n = 0

num : Val -> Nat
num v = plus (bitV (valOf R v pa) 8)
        (plus (bitV (valOf R v pb) 4)
        (plus (bitV (valOf R v (dia pa)) 2) (bitV (valOf R v (dia pb)) 1)))

-- s0 = 0, s1 = 1, s2 = 2, s3 = 3, s4 = 5, s5 = 7, s6 = 10, s7 = 11: the same
-- eight, in the order the closure happens to produce them.

lec_states : Eq (map num (Ust R)) (0 :: 5 :: 1 :: 10 :: 2 :: 11 :: 7 :: 3 :: [])
lec_states = refl

-- and the same profile: a and b true at two states each, Fa and Fb at five
-- each, F(a and b) at none -- which is the lecture's standing constraint,
-- derived here rather than assumed.

lec_profile : Eq (length (filterL (\ v -> valOf R v pa) (Ust R))
               :: length (filterL (\ v -> valOf R v pb) (Ust R))
               :: length (filterL (\ v -> valOf R v (dia pa)) (Ust R))
               :: length (filterL (\ v -> valOf R v (dia pb)) (Ust R))
               :: length (filterL (\ v -> valOf R v (dia (con pa pb))) (Ust R))
               :: []) (2 :: 2 :: 5 :: 5 :: 0 :: [])
lec_profile = refl

------------------------------------------------------------------------
-- The twenty-four edges.
--
-- The lecture lists  s0:1  s1:2  s2:2  s3:3  s4:3  s5:5  s6:3  s7:5 , which is
-- 24; here they come out in the closure's order, which by lec_states is
-- s0 s4 s1 s6 s2 s7 s5 s3.

lec_outdeg : Eq (map (\ v -> length (succs R (Ust R) v)) (Ust R))
                (1 :: 3 :: 2 :: 3 :: 2 :: 5 :: 5 :: 3 :: [])
lec_outdeg = refl

lec_edges : Eq (length (concatL (map (\ v -> succs R (Ust R) v) (Ust R)))) 24
lec_edges = refl

------------------------------------------------------------------------
-- The decision, and the lasso.
--
-- lassoOfDecide reads the countermodel as (start , rest , cycle), where rest is
-- the stem followed by the cycle.  Decoded, the run is  s7 s4 s0 s0 ...

lo : Prod Val (Prod (List Val) (List Val))
lo = lassoOfDecide fab (decide fab)

lec_notValid : Eq (isProof (decide fab) :: isProof (decideSCC fab) :: [])
                  (false :: false :: [])
lec_notValid = refl

-- Start, stem-and-cycle, cycle: s7, then s4 s0 s0, looping at s0.  Stated as
-- ONE equation because every mention of lo re-runs the whole countermodel
-- branch -- the elimination, Proposition 5.3 and the round construction, about
-- 4.7 s -- where isProof alone needs only the branch and takes 0.5 s.  The two
-- equations that mention lo are nine of this file's ten seconds; it is a worked
-- example and a benchmark, like LTL.Examples and LTL.Proofs, and the 5 s rule
-- of FORMALISATION-PLAN.md section 4a does not apply to it.

lec_run : Eq (prod (num (prodFst lo))
                   (prod (map num (prodFst (prodSnd lo)))
                         (map num (prodSnd (prodSnd lo)))))
             (prod 11 (prod (5 :: 0 :: 0 :: []) (0 :: [])))
lec_run = refl

------------------------------------------------------------------------
-- Why the lecture's path is not a countermodel.
--
-- s7 is the start of decide's run, s0 is its cycle.  evPred R A z is the
-- fairness predicate of LTL.SccLasso for the eventuality whose box-argument is
-- A: "the eventuality is not pending at z, or its body already fails there",
-- which for  F b  is the lecture's own  F_Fb = { v | v (Fb) = 0 or v (b) = 1 } .

s7 : Val
s7 = prodFst lo

s0 : Val
s0 = nth (prodSnd (prodSnd lo)) zero []

-- s7 is outside F_Fb, so the lecture's loop at s7 cannot be fair;
-- s0 is inside it, so the loop decide returns can be;
-- and s7 IS inside F_Fa, exactly as the lecture says, since a holds there.

lec_fair : Eq (evPred R (neg pb) s7 :: evPred R (neg pb) s0
            :: evPred R (neg pa) s7 :: []) (false :: true :: true :: [])
lec_fair = refl
