{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Examples -- Figure 11 of exLTL.pdf (Schmitt and Goubault-Larrecq,
-- "Linear Temporal Logic", page 14) run through decide.
--
-- Forty-six named modal and temporal statements, in the box/diamond fragment
-- -- no nxt occurs in any of them.  The figure's last column marks the ones its
-- procedure reports valid; here each is a checked equation instead, and the
-- checkmark is the BRANCH decide takes:
--
--   isProof (decide X) = true    decide returned inl, a derivation of X in L
--   isProof (decide X) = false   decide returned inr, a lasso countermodel
--                                together with  Deriv X -> Empty
--
-- So the file is not a comparison of two programs' outputs.  Every line below
-- is a theorem: the true ones assert that a derivation exists, the false ones
-- that none does, and both are certified by the type of decide (LTL.Decide).
--
-- The twenty-two marked in the figure are T, G, pb5, lin1, Dum, Dum1, Dum2,
-- Dum3, Dum4, D, 4, 4M, G0, H, H+, L, L+, L++, X, K3, K4, K5, and those are
-- exactly the twenty-two that come out true here.
--
-- The names are the figure's, with ax- prefixed where the figure's name is not
-- an Agda identifier (4, 5, 4M, 5M, +, ++).
--
-- The file takes about 17 s, which is forty-six decision problems and not one
-- proof: the 5 s rule of FORMALISATION-PLAN.md section 4a is a detector for
-- proofs that have drifted from the note, and does not apply to a benchmark.
-- The figure's own times are 0.017-0.083 s per formula for a procedure written
-- in ML; these run inside Agda's evaluator, on the decision procedure as a
-- type-theoretic boolean function, with no extraction anywhere.

module LTL.Examples where

open import LTL.Decide public

------------------------------------------------------------------------
-- The two variables

pv : Formula
pv = var zero

qv : Formula
qv = var (suc zero)

------------------------------------------------------------------------
-- The statements, in the figure's order

axT : Formula
axT = imp (box pv) pv

pb2 : Formula
pb2 = imp pv (box pv)

axG : Formula
axG = imp (dia (box pv)) (box (dia pv))

axM : Formula
axM = imp (box (dia pv)) (dia (box pv))

axM2 : Formula
axM2 = dia (box (imp pv (box pv)))

axM3 : Formula
axM3 = imp (con (box (dia pv)) (box (dia qv))) (dia (con pv qv))

pb5 : Formula
pb5 = imp pv (dia pv)

lin1 : Formula
lin1 = imp (con (dia pv) (dia qv))
           (dis (dia (con pv (dia qv))) (dia (con qv (dia pv))))

-- Dummett's axiom and its four variants
dumL : Formula
dumL = box (imp (box (imp pv (box pv))) pv)

dumLb : Formula
dumLb = box (imp (box (imp pv (box pv))) (box pv))

dumR : Formula
dumR = dia (box pv)

axDum : Formula
axDum = imp dumL (imp dumR pv)

axDum1 : Formula
axDum1 = imp dumL (imp dumR (box pv))

axDum2 : Formula
axDum2 = imp dumLb (imp dumR pv)

axDum3 : Formula
axDum3 = imp dumLb (imp dumR (box pv))

axDum4 : Formula
axDum4 = imp dumL (imp dumR (dis pv (box pv)))

axD : Formula
axD = imp (box pv) (dia pv)

ax4 : Formula
ax4 = imp (box pv) (box (box pv))

ax4M : Formula
ax4M = imp (con (box pv) (dia qv)) (dia (con (box pv) qv))

ax5 : Formula
ax5 = imp (dia pv) (box (dia pv))

ax5M : Formula
ax5M = imp (con (dia pv) (dia qv)) (dia (con (dia pv) qv))

axB : Formula
axB = imp pv (box (dia pv))

axBM : Formula
axBM = imp (con pv (dia qv)) (dia (con (dia pv) qv))

axG0 : Formula
axG0 = imp (dia (con pv (box qv))) (box (dis pv (dia qv)))

axH : Formula
axH = imp (con (box (dis pv qv))
               (con (box (dis (box pv) qv)) (box (dis pv (box qv)))))
          (dis (box pv) (box qv))

axHplus : Formula
axHplus = imp (con (box (dis (box pv) qv)) (box (dis pv (box qv))))
              (dis (box pv) (box qv))

axL : Formula
axL = dis (box (imp (con pv (box pv)) qv)) (box (imp (con qv (box qv)) pv))

axLplus : Formula
axLplus = dis (box (imp (box pv) qv)) (box (imp (box qv) pv))

axLplusplus : Formula
axLplusplus = dis (box (imp (box pv) (box qv))) (box (imp (box qv) (box pv)))

axPt : Formula
axPt = imp (box (dis pv (dia pv))) (dia (con pv (box pv)))

axW : Formula
axW = imp (box (imp (box pv) pv)) (box pv)

axZ : Formula
axZ = imp (box (imp (box pv) pv)) (imp (dia (box pv)) (box pv))

axGrz : Formula
axGrz = imp dumL pv

axGrz1 : Formula
axGrz1 = imp dumL (box pv)

axGrz2 : Formula
axGrz2 = imp dumLb pv

axGrz3 : Formula
axGrz3 = imp dumLb (box pv)

axGrz4 : Formula
axGrz4 = imp dumL (dis pv (box pv))

axGrz5 : Formula
axGrz5 = imp (con (box (imp (box (imp pv (box qv))) (box qv)))
                  (box (imp (box (imp (neg pv) (box qv))) (box qv))))
             (box qv)

axF : Formula
axF = dis (imp (dia (box pv)) qv) (box (imp (box qv) pv))

axHs : Formula
axHs = imp pv (box (imp (dia pv) pv))

axP : Formula
axP = imp (dia (box (dia pv))) (imp pv (box pv))

axR : Formula
axR = imp (dia (box pv)) (imp pv (box pv))

axX : Formula
axX = imp (box (box pv)) (box pv)

axZem : Formula
axZem = imp (box (dia (box pv))) (imp pv (box pv))

axK1 : Formula
axK1 = imp (dia pv) (box pv)

axK2 : Formula
axK2 = imp (box (dis pv qv)) (dis (box pv) (box qv))

axK3 : Formula
axK3 = iff (dia (box (dia pv))) (box (dia pv))

axK4 : Formula
axK4 = iff (box (dia (box pv))) (dia (box pv))

axK5 : Formula
axK5 = iff (box (dia (dis pv qv))) (dis (box (dia pv)) (box (dia qv)))

------------------------------------------------------------------------
-- The results

check_T : Eq (isProof (decide axT)) true
check_T = refl

check_pb2 : Eq (isProof (decide pb2)) false
check_pb2 = refl

check_G : Eq (isProof (decide axG)) true
check_G = refl

check_M : Eq (isProof (decide axM)) false
check_M = refl

check_M2 : Eq (isProof (decide axM2)) false
check_M2 = refl

check_M3 : Eq (isProof (decide axM3)) false
check_M3 = refl

check_pb5 : Eq (isProof (decide pb5)) true
check_pb5 = refl

check_lin1 : Eq (isProof (decide lin1)) true
check_lin1 = refl

check_Dum : Eq (isProof (decide axDum)) true
check_Dum = refl

check_Dum1 : Eq (isProof (decide axDum1)) true
check_Dum1 = refl

check_Dum2 : Eq (isProof (decide axDum2)) true
check_Dum2 = refl

check_Dum3 : Eq (isProof (decide axDum3)) true
check_Dum3 = refl

check_Dum4 : Eq (isProof (decide axDum4)) true
check_Dum4 = refl

check_D : Eq (isProof (decide axD)) true
check_D = refl

check_ax4 : Eq (isProof (decide ax4)) true
check_ax4 = refl

check_ax4M : Eq (isProof (decide ax4M)) true
check_ax4M = refl

check_ax5 : Eq (isProof (decide ax5)) false
check_ax5 = refl

check_ax5M : Eq (isProof (decide ax5M)) false
check_ax5M = refl

check_B : Eq (isProof (decide axB)) false
check_B = refl

check_BM : Eq (isProof (decide axBM)) false
check_BM = refl

check_G0 : Eq (isProof (decide axG0)) true
check_G0 = refl

check_H : Eq (isProof (decide axH)) true
check_H = refl

check_Hplus : Eq (isProof (decide axHplus)) true
check_Hplus = refl

check_L : Eq (isProof (decide axL)) true
check_L = refl

check_Lplus : Eq (isProof (decide axLplus)) true
check_Lplus = refl

check_Lplusplus : Eq (isProof (decide axLplusplus)) true
check_Lplusplus = refl

check_Pt : Eq (isProof (decide axPt)) false
check_Pt = refl

check_W : Eq (isProof (decide axW)) false
check_W = refl

check_Z : Eq (isProof (decide axZ)) false
check_Z = refl

check_Grz : Eq (isProof (decide axGrz)) false
check_Grz = refl

check_Grz1 : Eq (isProof (decide axGrz1)) false
check_Grz1 = refl

check_Grz2 : Eq (isProof (decide axGrz2)) false
check_Grz2 = refl

check_Grz3 : Eq (isProof (decide axGrz3)) false
check_Grz3 = refl

check_Grz4 : Eq (isProof (decide axGrz4)) false
check_Grz4 = refl

check_Grz5 : Eq (isProof (decide axGrz5)) false
check_Grz5 = refl

check_F : Eq (isProof (decide axF)) false
check_F = refl

check_Hs : Eq (isProof (decide axHs)) false
check_Hs = refl

check_P : Eq (isProof (decide axP)) false
check_P = refl

check_R : Eq (isProof (decide axR)) false
check_R = refl

check_X : Eq (isProof (decide axX)) true
check_X = refl

check_Zem : Eq (isProof (decide axZem)) false
check_Zem = refl

check_K1 : Eq (isProof (decide axK1)) false
check_K1 = refl

check_K2 : Eq (isProof (decide axK2)) false
check_K2 = refl

check_K3 : Eq (isProof (decide axK3)) true
check_K3 = refl

check_K4 : Eq (isProof (decide axK4)) true
check_K4 = refl

check_K5 : Eq (isProof (decide axK5)) true
check_K5 = refl

------------------------------------------------------------------------
-- Two of the countermodels, read off.
--
-- decide returns the lasso as a record; cmStart, cmRest and cmCycle give the
-- states as the procedure stores them, but a bit vector read against
-- sub (neg Q) is not something one wants to look at.  traceOf evaluates a
-- chosen formula at the successive stages of the run instead, and shapeOf says
-- where the run starts repeating: with shapeOf Q = prod r c the run is
--
--    v0 , rest_0 , ... , rest_{r-1} , then the last c of those, forever
--
-- so it is periodic from stage  1 + r - c  on, with period c.
--
-- Nothing here is an extra assumption.  traceOf goes through eval of LTL.Eval,
-- which is the semantics soundness (G26) is proved against, so
-- "traceOf Q Q 1 = false :: []" below and the Deriv Q -> Empty field of the
-- record are the same fact seen from the two ends.

------------------------------------------------------------------------
-- pb2 = p -> box p.
--
-- shapeOf pb2 = prod 3 1: three states then a fixed point, so the run is
--
--    p       1  0  1  1  1  1  1  1  ...
--    box p   0  0  1  1
--    pb2     0  1  1  1
--
-- p holds now and fails at the next stage, which refutes box p now; from
-- stage 2 on p holds forever, so box p holds and pb2 holds at every stage but
-- the first.  That single false at stage 0 is the countermodel.

pb2_shape : Eq (shapeOf pb2) (prod 3 1)
pb2_shape = refl

pb2_p : Eq (traceOf pb2 pv 8)
           (true :: false :: true :: true :: true :: true :: true :: true :: [])
pb2_p = refl

pb2_box : Eq (traceOf pb2 (box pv) 4) (false :: false :: true :: true :: [])
pb2_box = refl

pb2_input : Eq (traceOf pb2 pb2 4) (false :: true :: true :: true :: [])
pb2_input = refl

------------------------------------------------------------------------
-- axM2 = dia (box (p -> box p)).
--
-- shapeOf axM2 = prod 2 2: the cycle has two states and the stem is empty, so
-- the run is periodic from stage 1 with period 2 --
--
--    p            1  0  1  0  1  0  1  0  ...
--    p -> box p   0  1  0  1  0  1  0  1
--    axM2         0  0  0  0
--
-- p alternates forever, so box p is false at every stage, so p -> box p fails
-- at exactly the stages where p holds -- infinitely often.  Hence
-- box (p -> box p) holds nowhere and its diamond is false at every stage: the
-- alternating run refutes axM2 not just at stage 0 but everywhere, which is
-- what an eventuality being unfulfillable on a cycle looks like.

axM2_shape : Eq (shapeOf axM2) (prod 2 2)
axM2_shape = refl

axM2_p : Eq (traceOf axM2 pv 8)
            (true :: false :: true :: false :: true :: false :: true :: false :: [])
axM2_p = refl

axM2_step : Eq (traceOf axM2 (imp pv (box pv)) 8)
               (false :: true :: false :: true :: false :: true :: false :: true :: [])
axM2_step = refl

axM2_input : Eq (traceOf axM2 axM2 4) (false :: false :: false :: false :: [])
axM2_input = refl

------------------------------------------------------------------------
-- The half of K5 that carries the content.
--
--   box dia (p or q)  ->  box dia p  or  box dia q
--
-- The figure lists K5 as the equivalence; this is its left-to-right half, and
-- it is the only half that is not immediate.  Semantically it is the statement
-- that if p or q holds infinitely often then one of the two does, which on
-- paper is a pigeonhole argument about an infinite run.  Formally there is no
-- infinite run and no pigeonhole: nothing here is coinductive, and the argument
-- is the elimination of Definition 3.1 followed by Theorem 4.1.
--
-- Measured.  Sub of the negation has length 22, so the naive state space is
-- 2^22 = 4194304 vectors.  The atoms are p, q and the six box-subformulas
--
--    box (neg (p or q)) , box dia (p or q) , box (neg p) , box dia p ,
--    box (neg q) , box dia q
--
-- so 2^8 = 256 assignments are built, 59 of them are states, and the closure of
-- the ones containing the negation has 9 members.  The elimination then runs
--
--    9  ->  8  ->  4  ->  0
--
-- and EVERY removal goes by (R2).  Not one state is dropped for want of a
-- successor: the whole refutation is the loop-invariant case, which is what one
-- would expect of a formula that says an eventuality recurring forever must
-- recur in one of two ways.  So this example exercises extractR2 -- the
-- invariant B = beta_W, (Ind) through indRule, the greatest fixed point of
-- LTL.Gfp -- nine states deep, where bnb exercises it once.
--
-- decide returns inl in 0.9 s.  Before Phase 8 the state list alone would have
-- been 2^22 vectors filtered one at a time; it is the atom generator of G30
-- that makes the example reachable at all.

axK5fwd : Formula
axK5fwd = imp (box (dia (dis pv qv))) (dis (box (dia pv)) (box (dia qv)))

K5fwd_sub : Eq (length (sub (neg axK5fwd))) 22
K5fwd_sub = refl

K5fwd_atoms : Eq (length (atoms (sub (neg axK5fwd)))) 8
K5fwd_atoms = refl

K5fwd_cands : Eq (length (cands (neg axK5fwd))) 256
K5fwd_cands = refl

K5fwd_states : Eq (length (StC (neg axK5fwd))) 59
K5fwd_states = refl

K5fwd_closure : Eq (length (Ust (neg axK5fwd))) 9
K5fwd_closure = refl

-- the first round removes one state, and by (R2)

K5fwd_round1 : Eq (reasons (neg axK5fwd) (Ust (neg axK5fwd))) (false :: [])
K5fwd_round1 = refl

K5fwd_uinf : Eq (length (Uinf (neg axK5fwd))) 0
K5fwd_uinf = refl

check_K5fwd : Eq (isProof (decide axK5fwd)) true
check_K5fwd = refl
