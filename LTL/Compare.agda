{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Compare -- checkpoint C8 of PHASE11-PLAN.md: the three procedures set
-- against each other.
--
-- Kept out of LTL.Proofs deliberately.  This file is a BENCHMARK -- it runs
-- forty-seven decision problems through a second decision procedure -- and the
-- 5 s rule of FORMALISATION-PLAN.md section 4a is a detector for proofs that
-- have drifted from the note, not a budget for measurements.  LTL.Examples is
-- on the same side of that line and for the same reason.
--
-- C8 asks three things.
--
-- 1. AGREEMENT.  isProof (decideSCC X) = isProof (decide X) for every statement
--    of LTL.Examples.  Each agree_X below is that equation, and it is a theorem
--    about the two PROCEDURES, not a comparison of two printouts: both sides
--    are closed booleans and refl checks them.  It is proved as scc_X composed
--    with LTL.Examples' own check_X rather than by one refl on the pair, so
--    that decide is not run a second time -- agreeOn is the composition and it
--    is the only inference in the file.
--
--    All forty-seven agree.  Twenty-two are proofs and twenty-five are
--    countermodels, exactly as the figure and LTL.Examples record.
--
-- 2. THE LASSO ON THE C5 FORMULA,  box (p or q) -> box p or box q .  The two
--    procedures return DIFFERENT countermodels, which is what the plan
--    anticipated and called the interesting observation:
--
--                    start          stem   cycle
--        decide      c5both           3      1
--        decideSCC   c5q              2      4
--
--    (the run stores stem ++ cycle, so the recorded rest lengths are 4 and 6).
--    decide starts where satB finds the first surviving state containing the
--    negation and closes the loop at the first repeated round boundary, giving
--    the single state at which p and q hold forever.  decideSCC starts where
--    ustSeedTo finds a seed reaching the terminal component and takes mkCirc's
--    cycle, which is one leg per eventuality prepended to the bare loop -- and
--    sub (neg c5) has three eventualities, so the cycle is four times round.
--    Both are countermodels and each carries its own  Deriv c5 -> Empty ; that
--    they differ is a fact about the two constructions and not a discrepancy.
--
-- 3. WALL CLOCK.  Measured on the machine of section 4g, cold, with the import
--    baseline (0.19 s) subtracted:
--
--                          decide     decideSCC
--        c5                 0.19 s      0.18 s      countermodel branch
--        axK5fwd            0.78 s      1.24 s      proof branch
--
--    The plan predicted SCC would be slower, "because mutual reachability is
--    quadratic in the component where gfpW is one removing pass".  Confirmed on
--    the proof branch, where it is 1.6x; refuted on the countermodel branch,
--    where the two are level.  The reason is visible in the code rather than in
--    the numbers.  On the proof branch decideSCC pays for reachSet and sccOf
--    over the whole of Ust P and pays nothing for the elimination, which it
--    never runs; on the countermodel branch it pays for BOTH -- the graph search
--    to find the component and uinfTrap to put the loop inside Uinf P -- but
--    saves the round construction and the boundary search of Proposition 5.3,
--    and on c5 those cancel.
--
--    So the phase's own summary stands: the SCC proof is the better explanation
--    and, on the branch where it is the whole story, the worse implementation.
--
--    Across the whole suite the two are level, and neither figure is a clean
--    per-procedure time: LTL.Examples is 23.1 s for decide's forty-seven plus
--    its structural checks (state counts, closures, two countermodels read
--    off), and this file is 20.8 s for decideSCC's forty-seven plus the C5
--    lassos.  The controlled comparison is the two-line table above.
--
-- What the file does NOT claim.  Nothing here says the two procedures agree on
-- every formula -- that would be soundness and completeness of both, which is
-- what their TYPES already say, since each returns Deriv Q or a countermodel
-- carrying Deriv Q -> Empty.  Agreement on a list is a check that both are
-- actually running, not the reason to believe either.

module LTL.Compare where

open import LTL.DecideSCC public
open import LTL.Examples  public

------------------------------------------------------------------------
-- The only inference in the file.

agreeOn : (X : Formula) (b : Bool)
       -> Eq (isProof (decideSCC X)) b -> Eq (isProof (decide X)) b
       -> Eq (isProof (decideSCC X)) (isProof (decide X))
agreeOn X b e1 e2 = eqTrans e1 (eqSym e2)

------------------------------------------------------------------------
-- 1a. The forty-seven answers of decideSCC

scc_T : Eq (isProof (decideSCC axT)) true
scc_T = refl

scc_pb2 : Eq (isProof (decideSCC pb2)) false
scc_pb2 = refl

scc_G : Eq (isProof (decideSCC axG)) true
scc_G = refl

scc_M : Eq (isProof (decideSCC axM)) false
scc_M = refl

scc_M2 : Eq (isProof (decideSCC axM2)) false
scc_M2 = refl

scc_M3 : Eq (isProof (decideSCC axM3)) false
scc_M3 = refl

scc_pb5 : Eq (isProof (decideSCC pb5)) true
scc_pb5 = refl

scc_lin1 : Eq (isProof (decideSCC lin1)) true
scc_lin1 = refl

scc_Dum : Eq (isProof (decideSCC axDum)) true
scc_Dum = refl

scc_Dum1 : Eq (isProof (decideSCC axDum1)) true
scc_Dum1 = refl

scc_Dum2 : Eq (isProof (decideSCC axDum2)) true
scc_Dum2 = refl

scc_Dum3 : Eq (isProof (decideSCC axDum3)) true
scc_Dum3 = refl

scc_Dum4 : Eq (isProof (decideSCC axDum4)) true
scc_Dum4 = refl

scc_D : Eq (isProof (decideSCC axD)) true
scc_D = refl

scc_ax4 : Eq (isProof (decideSCC ax4)) true
scc_ax4 = refl

scc_ax4M : Eq (isProof (decideSCC ax4M)) true
scc_ax4M = refl

scc_ax5 : Eq (isProof (decideSCC ax5)) false
scc_ax5 = refl

scc_ax5M : Eq (isProof (decideSCC ax5M)) false
scc_ax5M = refl

scc_B : Eq (isProof (decideSCC axB)) false
scc_B = refl

scc_BM : Eq (isProof (decideSCC axBM)) false
scc_BM = refl

scc_G0 : Eq (isProof (decideSCC axG0)) true
scc_G0 = refl

scc_H : Eq (isProof (decideSCC axH)) true
scc_H = refl

scc_Hplus : Eq (isProof (decideSCC axHplus)) true
scc_Hplus = refl

scc_L : Eq (isProof (decideSCC axL)) true
scc_L = refl

scc_Lplus : Eq (isProof (decideSCC axLplus)) true
scc_Lplus = refl

scc_Lplusplus : Eq (isProof (decideSCC axLplusplus)) true
scc_Lplusplus = refl

scc_Pt : Eq (isProof (decideSCC axPt)) false
scc_Pt = refl

scc_W : Eq (isProof (decideSCC axW)) false
scc_W = refl

scc_Z : Eq (isProof (decideSCC axZ)) false
scc_Z = refl

scc_Grz : Eq (isProof (decideSCC axGrz)) false
scc_Grz = refl

scc_Grz1 : Eq (isProof (decideSCC axGrz1)) false
scc_Grz1 = refl

scc_Grz2 : Eq (isProof (decideSCC axGrz2)) false
scc_Grz2 = refl

scc_Grz3 : Eq (isProof (decideSCC axGrz3)) false
scc_Grz3 = refl

scc_Grz4 : Eq (isProof (decideSCC axGrz4)) false
scc_Grz4 = refl

scc_Grz5 : Eq (isProof (decideSCC axGrz5)) false
scc_Grz5 = refl

scc_F : Eq (isProof (decideSCC axF)) false
scc_F = refl

scc_Hs : Eq (isProof (decideSCC axHs)) false
scc_Hs = refl

scc_P : Eq (isProof (decideSCC axP)) false
scc_P = refl

scc_R : Eq (isProof (decideSCC axR)) false
scc_R = refl

scc_X : Eq (isProof (decideSCC axX)) true
scc_X = refl

scc_Zem : Eq (isProof (decideSCC axZem)) false
scc_Zem = refl

scc_K1 : Eq (isProof (decideSCC axK1)) false
scc_K1 = refl

scc_K2 : Eq (isProof (decideSCC axK2)) false
scc_K2 = refl

scc_K3 : Eq (isProof (decideSCC axK3)) true
scc_K3 = refl

scc_K4 : Eq (isProof (decideSCC axK4)) true
scc_K4 = refl

scc_K5 : Eq (isProof (decideSCC axK5)) true
scc_K5 = refl

scc_K5fwd : Eq (isProof (decideSCC axK5fwd)) true
scc_K5fwd = refl

------------------------------------------------------------------------
-- 1b. and that they are the answers of decide

agree_T : Eq (isProof (decideSCC axT)) (isProof (decide axT))
agree_T = agreeOn axT true scc_T check_T

agree_pb2 : Eq (isProof (decideSCC pb2)) (isProof (decide pb2))
agree_pb2 = agreeOn pb2 false scc_pb2 check_pb2

agree_G : Eq (isProof (decideSCC axG)) (isProof (decide axG))
agree_G = agreeOn axG true scc_G check_G

agree_M : Eq (isProof (decideSCC axM)) (isProof (decide axM))
agree_M = agreeOn axM false scc_M check_M

agree_M2 : Eq (isProof (decideSCC axM2)) (isProof (decide axM2))
agree_M2 = agreeOn axM2 false scc_M2 check_M2

agree_M3 : Eq (isProof (decideSCC axM3)) (isProof (decide axM3))
agree_M3 = agreeOn axM3 false scc_M3 check_M3

agree_pb5 : Eq (isProof (decideSCC pb5)) (isProof (decide pb5))
agree_pb5 = agreeOn pb5 true scc_pb5 check_pb5

agree_lin1 : Eq (isProof (decideSCC lin1)) (isProof (decide lin1))
agree_lin1 = agreeOn lin1 true scc_lin1 check_lin1

agree_Dum : Eq (isProof (decideSCC axDum)) (isProof (decide axDum))
agree_Dum = agreeOn axDum true scc_Dum check_Dum

agree_Dum1 : Eq (isProof (decideSCC axDum1)) (isProof (decide axDum1))
agree_Dum1 = agreeOn axDum1 true scc_Dum1 check_Dum1

agree_Dum2 : Eq (isProof (decideSCC axDum2)) (isProof (decide axDum2))
agree_Dum2 = agreeOn axDum2 true scc_Dum2 check_Dum2

agree_Dum3 : Eq (isProof (decideSCC axDum3)) (isProof (decide axDum3))
agree_Dum3 = agreeOn axDum3 true scc_Dum3 check_Dum3

agree_Dum4 : Eq (isProof (decideSCC axDum4)) (isProof (decide axDum4))
agree_Dum4 = agreeOn axDum4 true scc_Dum4 check_Dum4

agree_D : Eq (isProof (decideSCC axD)) (isProof (decide axD))
agree_D = agreeOn axD true scc_D check_D

agree_ax4 : Eq (isProof (decideSCC ax4)) (isProof (decide ax4))
agree_ax4 = agreeOn ax4 true scc_ax4 check_ax4

agree_ax4M : Eq (isProof (decideSCC ax4M)) (isProof (decide ax4M))
agree_ax4M = agreeOn ax4M true scc_ax4M check_ax4M

agree_ax5 : Eq (isProof (decideSCC ax5)) (isProof (decide ax5))
agree_ax5 = agreeOn ax5 false scc_ax5 check_ax5

agree_ax5M : Eq (isProof (decideSCC ax5M)) (isProof (decide ax5M))
agree_ax5M = agreeOn ax5M false scc_ax5M check_ax5M

agree_B : Eq (isProof (decideSCC axB)) (isProof (decide axB))
agree_B = agreeOn axB false scc_B check_B

agree_BM : Eq (isProof (decideSCC axBM)) (isProof (decide axBM))
agree_BM = agreeOn axBM false scc_BM check_BM

agree_G0 : Eq (isProof (decideSCC axG0)) (isProof (decide axG0))
agree_G0 = agreeOn axG0 true scc_G0 check_G0

agree_H : Eq (isProof (decideSCC axH)) (isProof (decide axH))
agree_H = agreeOn axH true scc_H check_H

agree_Hplus : Eq (isProof (decideSCC axHplus)) (isProof (decide axHplus))
agree_Hplus = agreeOn axHplus true scc_Hplus check_Hplus

agree_L : Eq (isProof (decideSCC axL)) (isProof (decide axL))
agree_L = agreeOn axL true scc_L check_L

agree_Lplus : Eq (isProof (decideSCC axLplus)) (isProof (decide axLplus))
agree_Lplus = agreeOn axLplus true scc_Lplus check_Lplus

agree_Lplusplus : Eq (isProof (decideSCC axLplusplus)) (isProof (decide axLplusplus))
agree_Lplusplus = agreeOn axLplusplus true scc_Lplusplus check_Lplusplus

agree_Pt : Eq (isProof (decideSCC axPt)) (isProof (decide axPt))
agree_Pt = agreeOn axPt false scc_Pt check_Pt

agree_W : Eq (isProof (decideSCC axW)) (isProof (decide axW))
agree_W = agreeOn axW false scc_W check_W

agree_Z : Eq (isProof (decideSCC axZ)) (isProof (decide axZ))
agree_Z = agreeOn axZ false scc_Z check_Z

agree_Grz : Eq (isProof (decideSCC axGrz)) (isProof (decide axGrz))
agree_Grz = agreeOn axGrz false scc_Grz check_Grz

agree_Grz1 : Eq (isProof (decideSCC axGrz1)) (isProof (decide axGrz1))
agree_Grz1 = agreeOn axGrz1 false scc_Grz1 check_Grz1

agree_Grz2 : Eq (isProof (decideSCC axGrz2)) (isProof (decide axGrz2))
agree_Grz2 = agreeOn axGrz2 false scc_Grz2 check_Grz2

agree_Grz3 : Eq (isProof (decideSCC axGrz3)) (isProof (decide axGrz3))
agree_Grz3 = agreeOn axGrz3 false scc_Grz3 check_Grz3

agree_Grz4 : Eq (isProof (decideSCC axGrz4)) (isProof (decide axGrz4))
agree_Grz4 = agreeOn axGrz4 false scc_Grz4 check_Grz4

agree_Grz5 : Eq (isProof (decideSCC axGrz5)) (isProof (decide axGrz5))
agree_Grz5 = agreeOn axGrz5 false scc_Grz5 check_Grz5

agree_F : Eq (isProof (decideSCC axF)) (isProof (decide axF))
agree_F = agreeOn axF false scc_F check_F

agree_Hs : Eq (isProof (decideSCC axHs)) (isProof (decide axHs))
agree_Hs = agreeOn axHs false scc_Hs check_Hs

agree_P : Eq (isProof (decideSCC axP)) (isProof (decide axP))
agree_P = agreeOn axP false scc_P check_P

agree_R : Eq (isProof (decideSCC axR)) (isProof (decide axR))
agree_R = agreeOn axR false scc_R check_R

agree_X : Eq (isProof (decideSCC axX)) (isProof (decide axX))
agree_X = agreeOn axX true scc_X check_X

agree_Zem : Eq (isProof (decideSCC axZem)) (isProof (decide axZem))
agree_Zem = agreeOn axZem false scc_Zem check_Zem

agree_K1 : Eq (isProof (decideSCC axK1)) (isProof (decide axK1))
agree_K1 = agreeOn axK1 false scc_K1 check_K1

agree_K2 : Eq (isProof (decideSCC axK2)) (isProof (decide axK2))
agree_K2 = agreeOn axK2 false scc_K2 check_K2

agree_K3 : Eq (isProof (decideSCC axK3)) (isProof (decide axK3))
agree_K3 = agreeOn axK3 true scc_K3 check_K3

agree_K4 : Eq (isProof (decideSCC axK4)) (isProof (decide axK4))
agree_K4 = agreeOn axK4 true scc_K4 check_K4

agree_K5 : Eq (isProof (decideSCC axK5)) (isProof (decide axK5))
agree_K5 = agreeOn axK5 true scc_K5 check_K5

agree_K5fwd : Eq (isProof (decideSCC axK5fwd)) (isProof (decide axK5fwd))
agree_K5fwd = agreeOn axK5fwd true scc_K5fwd check_K5fwd

------------------------------------------------------------------------
-- 2. The two lassos on the C5 formula.
--
-- lassoOfDecide reads a countermodel as (start , rest , cycle), where rest is
-- the run's stored remainder -- the stem followed by the cycle.

lassoLen : Prod Val (Prod (List Val) (List Val)) -> Prod Nat Nat
lassoLen (prod v (prod a b)) = prod (length a) (length b)

c5Decide : Prod Val (Prod (List Val) (List Val))
c5Decide = lassoOfDecide c5 (decide c5)

c5Scc : Prod Val (Prod (List Val) (List Val))
c5Scc = lassoOfDecide c5 (decideSCC c5)

c5_decide_start : Eq (valEq (prodFst c5Decide) c5both) true
c5_decide_start = refl

c5_scc_start : Eq (valEq (prodFst c5Scc) c5q) true
c5_scc_start = refl

c5_decide_len : Eq (lassoLen c5Decide) (prod 4 1)
c5_decide_len = refl

c5_scc_len : Eq (lassoLen c5Scc) (prod 6 4)
c5_scc_len = refl

-- and the observation itself: the two countermodels do not even start at the
-- same state.

c5_differ : Eq (valEq (prodFst c5Decide) (prodFst c5Scc)) false
c5_differ = refl
