{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Temporal -- G14 and G15 of FORMALISATION-PLAN.md.
--
-- Lemma 1.2 of m4.tex, the derived temporal rules (D1)-(D6), together with the
-- list forms of (D4) that Lemma 2.7 needs.
--
-- (D6) is the one to watch: it is the converse of the box A -> A and nxt (box A)
-- half of (Exp), and it is load-bearing twice over -- in Lemma 2.5, to refute
-- valuations violating (S2), and in Lemma 2.7, for the (T3) case.

module LTL.Temporal where

open import LTL.PropList public

------------------------------------------------------------------------
-- Projecting the two biconditional axioms

linF : {A : Formula} -> Deriv (imp (nxt (neg A)) (neg (nxt A)))
linF = mp conFst lin

linB : {A : Formula} -> Deriv (imp (neg (nxt A)) (nxt (neg A)))
linB = mp conSnd lin

boxElim : {A : Formula} -> Deriv (imp (box A) A)
boxElim = impTrans exp conFst

boxNxt : {A : Formula} -> Deriv (imp (box A) (nxt A))
boxNxt = impTrans exp (impTrans conSnd conFst)

boxNxtBox : {A : Formula} -> Deriv (imp (box A) (nxt (box A)))
boxNxtBox = impTrans exp (impTrans conSnd conSnd)

------------------------------------------------------------------------
-- (D1), (D2), (D3)

nxtGen : {A : Formula} -> Deriv A -> Deriv (nxt A)
nxtGen d = mp boxNxt (gen d)

nxtMono : {A B : Formula} -> Deriv (imp A B) -> Deriv (imp (nxt A) (nxt B))
nxtMono d = mp knxt (nxtGen d)

boxMono : {A B : Formula} -> Deriv (imp A B) -> Deriv (imp (box A) (box B))
boxMono d = mp kbox (gen d)

------------------------------------------------------------------------
-- nxt and bot

nxtTop : Deriv (nxt top)
nxtTop = nxtGen derivTop

nxtBot : Deriv (imp (nxt bot) bot)
nxtBot = mpU (mpU (liftP (exf {nxt top} {bot})) (liftP nxtTop)) linF

------------------------------------------------------------------------
-- (D4) for disjunction, binary.
--
-- dis A B is imp (neg A) B, so the first direction is (K nxt) composed with
-- the backward half of (Lin); the second is a case analysis on nxt A.

nxtDis1 : {A B : Formula}
       -> Deriv (imp (nxt (dis A B)) (dis (nxt A) (nxt B)))
nxtDis1 = impTransU (liftP linB) knxt

nxtDis2 : {A B : Formula}
       -> Deriv (imp (dis (nxt A) (nxt B)) (nxt (dis A B)))
nxtDis2 = caseU (liftP (nxtMono exf)) (impTransU identP (liftP (nxtMono p1)))

------------------------------------------------------------------------
-- Monotonicity of dis in its second argument

disMonoR : {X Y Z : Formula}
        -> Deriv (imp X Y) -> Deriv (imp (dis Z X) (dis Z Y))
disMonoR d = mp p2 (liftP d)

------------------------------------------------------------------------
-- (D4) for disjunction, over a list.
--
-- These are what Lemma 2.7 uses at both ends: nxtDisjL1 to pass from
-- |- nxt (beta St) to |- disj (map nxt (map chi St)), and nxtDisjL2 to come
-- back to |- chi v -> nxt (beta (succs v)).

nxtDisjL1 : (As : List Formula)
         -> Deriv (imp (nxt (disj As)) (disj (map nxt As)))
nxtDisjL1 []        = nxtBot
nxtDisjL1 (A :: As) = impTrans nxtDis1 (disMonoR (nxtDisjL1 As))

nxtDisjL2 : (As : List Formula)
         -> Deriv (imp (disj (map nxt As)) (nxt (disj As)))
nxtDisjL2 []        = exFalso
nxtDisjL2 (A :: As) = impTrans (disMonoR (nxtDisjL2 As)) nxtDis2

------------------------------------------------------------------------
-- (D4) for conjunction, the direction (D6) needs.
--
-- Derived without a formula-level conjunction introduction: nxt (con A B) is
-- nxt (neg X) with X = imp A (neg B), which by (Lin) is neg (nxt X), and
-- nxt X together with nxt A gives nxt (neg B), hence neg (nxt B).

nxtCon2 : {A B : Formula}
       -> Deriv (imp (con (nxt A) (nxt B)) (nxt (con A B)))
nxtCon2 {A} {B} = impTrans (negIntroU hB hNB) linB
  where
    P : Formula
    P = con (nxt A) (nxt B)

    X : Formula
    X = imp A (neg B)

    hB : Deriv (imp P (imp (nxt X) (nxt B)))
    hB = impTrans conSnd p1

    hNB : Deriv (imp P (imp (nxt X) (neg (nxt B))))
    hNB = impTransU (mpU2 (liftP knxt) (impTrans conFst p1)) (liftP linF)

------------------------------------------------------------------------
-- G15 : (D5) and (D6)

indRule : {A : Formula}
       -> Deriv (imp A (nxt A)) -> Deriv (imp A (box A))
indRule d = mp ind (gen d)

expConv : {A : Formula}
       -> Deriv (imp (con A (nxt (box A))) (box A))
expConv {A} = impTrans (indRule cToNxtC) (boxMono conFst)
  where
    cToNxtC : Deriv (imp (con A (nxt (box A))) (nxt (con A (nxt (box A)))))
    cToNxtC = impTrans (conPair (impTrans conSnd (nxtMono boxElim))
                                (impTrans conSnd (nxtMono boxNxtBox)))
                       nxtCon2

------------------------------------------------------------------------
-- The (S2) case of Lemma 2.5, now available.
--
-- A valuation with  box A  in v but  A  not in v  is refuted by (Exp); this
-- completes the list of shapes begun in LTL.Prop.

boxCase : {A C : Formula} -> Deriv (imp (box A) (imp (neg A) C))
boxCase = impTrans boxElim exf
