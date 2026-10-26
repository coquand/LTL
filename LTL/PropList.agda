{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.PropList -- G11 and G12 of FORMALISATION-PLAN.md.
--
-- (L2) and (L5) of Lemma 1.1 of m4.tex: the only two schemes indexed by a
-- list.  conj and disj are from LTL.Val, with conj [] = top and disj [] = bot,
-- the convention fixed after Lemma 1.1 -- so the two clauses of (L5) at n = 0
-- are exactly the two clauses of (L0).
--
-- disjElim is the workhorse of Phase 4: dropping refuted disjuncts, and taking
-- the disjunction over W in Theorem 4.1, are both instances of it.

module LTL.PropList where

open import LTL.Prop public
open import LTL.Val  public

------------------------------------------------------------------------
-- Negation introduction, lifted under an antecedent.
--
-- From  P -> (C -> B)  and  P -> (C -> neg B)  conclude  P -> neg C.  Every
-- refutation below factors through this.

mpU2 : {P Q A B : Formula}
    -> Deriv (imp P (imp Q (imp A B))) -> Deriv (imp P (imp Q A))
    -> Deriv (imp P (imp Q B))
mpU2 f g = mpU (mpU (liftP p2) f) g

negIntroU : {P C B : Formula}
         -> Deriv (imp P (imp C B)) -> Deriv (imp P (imp C (neg B)))
         -> Deriv (imp P (neg C))
negIntroU {P} {C} {B} f g =
  mpU (mpU (liftP (p3 {top} {neg C}))
           (mpU2 (mpU2 (liftP (liftP (exf {B} {neg top})))
                       (impTransU (liftP dne) f))
                 (impTransU (liftP dne) g)))
      (liftP derivTop)

------------------------------------------------------------------------
-- Binary conjunction.  con A B is neg (imp A (neg B)).

conFst : {A B : Formula} -> Deriv (imp (con A B) A)
conFst {A} {B} = mp p3 (impTrans (negElim {A} {neg B}) dni)

conSnd : {A B : Formula} -> Deriv (imp (con A B) B)
conSnd {A} {B} = mp p3 (impTrans (p1 {neg B} {A}) dni)

conPair : {C A B : Formula}
       -> Deriv (imp C A) -> Deriv (imp C B) -> Deriv (imp C (con A B))
conPair f g = mp p3 (negIntroU (liftP g) (impTransU (liftP f) dne))

-- Case analysis under an antecedent: from P -> (X -> Z) and P -> (neg X -> Z)
-- conclude P -> Z.  This is the cons case of disjElim isolated, and it is what
-- the (D4) disjunction lemmas of Phase 3 need.

caseU : {P X Z : Formula}
     -> Deriv (imp P (imp X Z)) -> Deriv (imp P (imp (neg X) Z))
     -> Deriv (imp P Z)
caseU {P} {X} {Z} f g = impTrans (negIntroU h1 h2) dne
  where
    h1 : Deriv (imp P (imp (neg Z) X))
    h1 = impTransU (mpU (liftP (contra {neg X} {Z})) g) (liftP dne)

    h2 : Deriv (imp P (imp (neg Z) (neg X)))
    h2 = mpU (liftP (contra {X} {Z})) f

------------------------------------------------------------------------
-- G11 : (L2)

data AllD (C : Formula) : List Formula -> Set where
  adNil  : AllD C []
  adCons : {A : Formula} {As : List Formula}
        -> Deriv (imp C A) -> AllD C As -> AllD C (A :: As)

allD_map : {C : Formula} (As : List Formula)
        -> ({A : Formula} -> Mem A As -> Deriv (imp C A)) -> AllD C As
allD_map []        f = adNil
allD_map (A :: As) f = adCons (f memHd) (allD_map As (\ m -> f (memTl m)))

conjProj : {A : Formula} (As : List Formula)
        -> Mem A As -> Deriv (imp (conj As) A)
conjProj []        ()
conjProj (B :: Bs) memHd     = conFst
conjProj (B :: Bs) (memTl h) = impTrans conSnd (conjProj Bs h)

conjIntro : {C : Formula} (As : List Formula)
         -> AllD C As -> Deriv (imp C (conj As))
conjIntro []        adNil         = liftP derivTop
conjIntro (A :: As) (adCons d ds) = conPair d (conjIntro As ds)

------------------------------------------------------------------------
-- G12 : (L5)

data AllI (C : Formula) : List Formula -> Set where
  aiNil  : AllI C []
  aiCons : {A : Formula} {As : List Formula}
        -> Deriv (imp A C) -> AllI C As -> AllI C (A :: As)

allI_map : {C : Formula} (As : List Formula)
        -> ({A : Formula} -> Mem A As -> Deriv (imp A C)) -> AllI C As
allI_map []        f = aiNil
allI_map (A :: As) f = aiCons (f memHd) (allI_map As (\ m -> f (memTl m)))

disjIntro : {A : Formula} (As : List Formula)
         -> Mem A As -> Deriv (imp A (disj As))
disjIntro []        ()
disjIntro (B :: Bs) memHd     = exf
disjIntro (B :: Bs) (memTl h) = impTrans (disjIntro Bs h) p1

-- The cons case is the classical one: under the antecedent
-- P = neg A -> disj As, contraposing the two hypotheses gives
-- neg C -> A and neg C -> neg A, hence neg (neg C), hence C.

disjElim : {C : Formula} (As : List Formula)
        -> AllI C As -> Deriv (imp (disj As) C)
disjElim []        aiNil         = exFalso
disjElim {C} (A :: As) (aiCons d ds) = impTrans (negIntroU h1 h2) dne
  where
    P : Formula
    P = imp (neg A) (disj As)

    hIH : Deriv (imp (disj As) C)
    hIH = disjElim As ds

    hNA : Deriv (imp P (imp (neg A) C))
    hNA = impTransU identP (liftP hIH)

    h1 : Deriv (imp P (imp (neg C) A))
    h1 = impTransU (mpU (liftP (contra {neg A} {C})) hNA) (liftP dne)

    h2 : Deriv (imp P (imp (neg C) (neg A)))
    h2 = mpU (liftP (contra {A} {C})) (liftP d)

------------------------------------------------------------------------
-- Monotonicity of disj.
--
-- This is what "dropping the refuted disjuncts" comes to in Lemma 2.6 and
-- Lemma 2.7, and what step (ii) of Theorem 4.1 needs to pass from
-- beta (succs w) to B.

disjMono : (As Bs : List Formula)
        -> ({A : Formula} -> Mem A As -> Mem A Bs)
        -> Deriv (imp (disj As) (disj Bs))
disjMono As Bs sb = disjElim As (allI_map As (\ m -> disjIntro Bs (sb m)))

conjMono : (As Bs : List Formula)
        -> ({A : Formula} -> Mem A Bs -> Mem A As)
        -> Deriv (imp (conj As) (conj Bs))
conjMono As Bs sb = conjIntro Bs (allD_map Bs (\ m -> conjProj As (sb m)))

-- Dropping a single refuted disjunct.  Lemma 2.6 discharges the non-states
-- this way, and Lemma 2.7 the successors w with v not-> w.

disjDrop : {A : Formula} (As : List Formula)
        -> Deriv (neg A) -> Deriv (imp (disj (A :: As)) (disj As))
disjDrop {A} As d =
  disjElim (A :: As)
           (aiCons (mp negElim d) (allI_map As (\ m -> disjIntro As m)))

------------------------------------------------------------------------
-- G13 : (L6)
--
-- If  |- disj Cs  then  |- disj (splitOn A Cs) , where splitOn A Cs conjoins
-- each disjunct with A and, separately, with neg A.  This is the step of the
-- structural induction along Sub P in Lemma 2.6.

splitOn : Formula -> List Formula -> List Formula
splitOn A Cs = append (map (con A) Cs) (map (con (neg A)) Cs)

-- From  neg (U and C)  and C, conclude  neg U.  Both halves of splitD use it,
-- once at U := A and once at U := neg A.

conNegL : {U C : Formula} -> Deriv (imp (neg (con U C)) (imp C (neg U)))
conNegL {U} {C} = impTransU (liftP dni) (mpU (liftP (contra {U} {neg C})) dne)

splitD : {A : Formula} (Cs : List Formula)
      -> Deriv (disj Cs) -> Deriv (disj (splitOn A Cs))
splitD {A} Cs d = mp (disjElim Cs (allI_map Cs each)) d
  where
    Z : Formula
    Z = disj (splitOn A Cs)

    each : {C : Formula} -> Mem C Cs -> Deriv (imp C Z)
    each {C} m = impTrans (negIntroU h1 h2) dne
      where
        j1 : Deriv (imp (con A C) Z)
        j1 = disjIntro (splitOn A Cs)
               (memAppL (map (con A) Cs) (map (con (neg A)) Cs)
                        (memMap (con A) m))

        j2 : Deriv (imp (con (neg A) C) Z)
        j2 = disjIntro (splitOn A Cs)
               (memAppR (map (con A) Cs) (map (con (neg A)) Cs)
                        (memMap (con (neg A)) m))

        -- neg Z gives neg (neg A and C), which with C gives neg (neg A),
        -- hence A.
        h1 : Deriv (imp C (imp (neg Z) A))
        h1 = impTransU (impTransU (liftP (mp contra j2))
                                  (impSwap (conNegL {neg A} {C})))
                       (liftP dne)

        -- neg Z gives neg (A and C), which with C gives neg A.
        h2 : Deriv (imp C (imp (neg Z) (neg A)))
        h2 = impTransU (liftP (mp contra j1))
                       (impSwap (conNegL {A} {C}))
