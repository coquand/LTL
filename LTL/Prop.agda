{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Prop -- G9 and G10 of FORMALISATION-PLAN.md.
--
-- The list-free part of Lemma 1.1 of m4.tex: (L1), (L0), (L3), (L4), (L7).
--
-- Everything here comes from (P1), (P2), (P3) by composition.  There is no
-- deduction theorem and no tautology checker; hypothetical reasoning is done
-- by imp-lifting under a fixed antecedent P, with the three combinators
--
--     identP : Deriv (imp P P)
--     liftP  : Deriv A -> Deriv (imp P A)
--     mpU    : Deriv (imp P (imp A B)) -> Deriv (imp P A) -> Deriv (imp P B)
--
-- which is the style of ~/CHWISTEK/T4/CARNEIRO-WITNESS-IMP-LIFTING.md.

module LTL.Prop where

open import LTL.Deriv public

------------------------------------------------------------------------
-- G9 : (L1)

-- I = SKK
impRefl : {A : Formula} -> Deriv (imp A A)
impRefl {A} = mp (mp p2 (p1 {A} {imp A A})) (p1 {A} {A})

weaken : {A B : Formula} -> Deriv B -> Deriv (imp A B)
weaken d = mp p1 d

impTrans : {A B C : Formula}
        -> Deriv (imp A B) -> Deriv (imp B C) -> Deriv (imp A C)
impTrans f g = mp (mp p2 (weaken g)) f

------------------------------------------------------------------------
-- The imp-lifting combinators.
--
-- identP and liftP are impRefl and weaken under other names; mpU is modus
-- ponens performed under the antecedent P.  Together they replace the
-- deduction theorem for every use below.

identP : {P : Formula} -> Deriv (imp P P)
identP = impRefl

liftP : {P A : Formula} -> Deriv A -> Deriv (imp P A)
liftP = weaken

mpU : {P A B : Formula}
   -> Deriv (imp P (imp A B)) -> Deriv (imp P A) -> Deriv (imp P B)
mpU f g = mp (mp p2 f) g

impTransU : {P A B C : Formula}
         -> Deriv (imp P (imp A B)) -> Deriv (imp P (imp B C))
         -> Deriv (imp P (imp A C))
impTransU f g = mpU (mpU (liftP p2) (impTrans g p1)) f

impSwap : {A B C : Formula}
       -> Deriv (imp A (imp B C)) -> Deriv (imp B (imp A C))
impSwap {A} {B} {C} f = mpU (weaken (mp p2 f)) (p1 {B} {A})

------------------------------------------------------------------------
-- G10 : (L7), then (L3), (L0), (L4)

-- (L7) first half.  This is what the  v (imp A B) = 0  case of Lemma 2.5
-- needs, together with p1 as its second half.
negElim : {A B : Formula} -> Deriv (imp (neg A) (imp A B))
negElim = impTrans p1 p3

impIntroL : {A B : Formula} -> Deriv (imp (neg A) (imp A B))
impIntroL = negElim

impIntroR : {A B : Formula} -> Deriv (imp B (imp A B))
impIntroR = p1

-- (L3)
exf : {A B : Formula} -> Deriv (imp A (imp (neg A) B))
exf = impSwap negElim

------------------------------------------------------------------------
-- top and bot

derivTop : Deriv top
derivTop = impRefl

-- Double negation.  dne comes first: under the antecedent  neg (neg A)  we
-- have  neg A -> neg top  by negElim, hence  top -> A  by (P3), and  top  is
-- available, so A follows.

dne : {A : Formula} -> Deriv (imp (neg (neg A)) A)
dne {A} = mpU (impTrans (negElim {neg A} {neg top}) (p3 {top} {A}))
              (liftP derivTop)

dni : {A : Formula} -> Deriv (imp A (neg (neg A)))
dni {A} = mp (p3 {A} {neg (neg A)}) (dne {neg A})

-- (L0)
notBot : Deriv (neg bot)
notBot = mp dni derivTop

exFalso : {C : Formula} -> Deriv (imp bot C)
exFalso = mpU (negElim {top}) (liftP derivTop)

-- (L4).  Since  dis A B  is  imp (neg A) B , excluded middle is reflexivity.
lem : {A : Formula} -> Deriv (dis A (neg A))
lem = impRefl

------------------------------------------------------------------------
-- Contraposition, used by the disjunction lemmas of G12

dnMono : {A B : Formula}
      -> Deriv (imp (imp A B) (imp (neg (neg A)) (neg (neg B))))
dnMono = impTransU (impTransU (liftP dne) identP) (liftP dni)

contra : {A B : Formula} -> Deriv (imp (imp A B) (imp (neg B) (neg A)))
contra {A} {B} = impTrans dnMono (p3 {neg B} {neg A})

------------------------------------------------------------------------
-- Checkpoint C2.
--
-- Composition as a theorem rather than a rule -- a test that the three
-- combinators really do replace the deduction theorem.

impComp : {A B C : Formula}
       -> Deriv (imp (imp A B) (imp (imp B C) (imp A C)))
impComp = impSwap (impTrans p1 p2)

------------------------------------------------------------------------
-- The four propositional shapes required by Lemma 2.5 of m4.tex.
--
-- Lemma 2.5 refutes a valuation violating (S1) by exhibiting a contradiction
-- among finitely many conjuncts of chi_v.  Each violation has a fixed shape,
-- and each shape is a fixed scheme -- there is nothing here a tautology
-- checker would be needed for.  Listed with the violation they discharge:
--
--   negCase1  v (neg A) = 1  and  v A = 1
--   negCase0  v (neg A) = 0  and  v A = 0
--   impCase1  v (imp A B) = 1  but  v A = 1, v B = 0
--   impCase0L v (imp A B) = 0  but  v A = 0
--   impCase0R v (imp A B) = 0  but  v B = 1
--
-- The (S2) violation needs (Exp), so it belongs to Phase 3.

negCase1 : {A C : Formula} -> Deriv (imp A (imp (neg A) C))
negCase1 = exf

negCase0 : {A C : Formula} -> Deriv (imp (neg (neg A)) (imp (neg A) C))
negCase0 {A} {C} = negElim {neg A} {C}

impCase1 : {A B C : Formula}
        -> Deriv (imp (imp A B) (imp A (imp (neg B) C)))
impCase1 = impTransU identP (liftP exf)

impCase0L : {A B C : Formula}
         -> Deriv (imp (neg A) (imp (neg (imp A B)) C))
impCase0L = impTrans negElim exf

impCase0R : {A B C : Formula}
         -> Deriv (imp B (imp (neg (imp A B)) C))
impCase0R = impTrans p1 exf
