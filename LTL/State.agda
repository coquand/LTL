{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.State -- G5 of FORMALISATION-PLAN.md.
--
-- Definition 2.2 of m4.tex: a valuation is a state when it respects the
-- connectives (S1) and satisfies  box A in v  implies  A in v  (S2).
--
-- To these the formalisation adds a third clause, coherence on duplicates.
-- It has no counterpart in the note because there a state IS a function on the
-- set Sub(phi); here a valuation is a List Bool read positionally against a
-- list that repeats (LTL.Sub, subBenAri_dup).  The clause is exactly what makes
-- the vector represent a function on the set, so isState is the faithful
-- encoding of Definition 2.2 rather than a strengthening of it.

module LTL.State where

open import LTL.Val public

------------------------------------------------------------------------
-- Lookup by first occurrence.
--
-- valOf P v A is the bit v assigns to A, read at the FIRST position of sub P
-- carrying A.  Under coherence this agrees with the bit at every position
-- carrying A, which is what lets chi (built positionally) and the conditions
-- below (built by lookup) be about the same thing.

valOf : Formula -> Val -> Formula -> Bool
valOf P v A = bitAt v (idx (sub P) A)

------------------------------------------------------------------------
-- (S1) and (S2), imposed at each member of sub P.
--
-- var and nxt carry no local condition: the behaviour of nxt lives entirely in
-- the transition relation (LTL.Step), which is the point of Remark 2.1.

okAt : Formula -> Val -> Formula -> Bool
okAt P v (var n)   = true
okAt P v (neg A)   = boolEq (valOf P v (neg A)) (boolNot (valOf P v A))
okAt P v (imp A B) = boolEq (valOf P v (imp A B))
                            (boolImp (valOf P v A) (valOf P v B))
okAt P v (nxt A)   = true
okAt P v (box A)   = boolImp (valOf P v (box A)) (valOf P v A)

allOk : Formula -> Val -> List Formula -> Bool
allOk P v []        = true
allOk P v (A :: As) = boolAnd (okAt P v A) (allOk P v As)

------------------------------------------------------------------------
-- Coherence on duplicates.
--
-- Stated as "every position agrees with the first occurrence of its formula",
-- which is linear rather than quadratic and equivalent by transitivity through
-- that first occurrence.

cohAt : Formula -> Val -> Nat -> Bool
cohAt P v i = boolEq (bitAt v i) (valOf P v (nth (sub P) i bot))

allCoh : Formula -> Val -> Nat -> Bool
allCoh P v zero    = true
allCoh P v (suc n) = boolAnd (cohAt P v n) (allCoh P v n)

------------------------------------------------------------------------
-- States

isState : Formula -> Val -> Bool
isState P v = boolAnd (allOk P v (sub P))
                      (allCoh P v (length (sub P)))

St : Formula -> List Val
St P = filterL (isState P) (allVecs (length (sub P)))

------------------------------------------------------------------------
-- Searching allOk

allOk_at : (P : Formula) (v : Val) (As : List Formula) {A : Formula}
        -> Mem A As -> Eq (allOk P v As) true -> Eq (okAt P v A) true
allOk_at P v []        ()        e
allOk_at P v (B :: Bs) memHd     e = andTrueL (okAt P v B) (allOk P v Bs) e
allOk_at P v (B :: Bs) (memTl m) e =
  allOk_at P v Bs m (andTrueR (okAt P v B) (allOk P v Bs) e)

allOk_false : (P : Formula) (v : Val) (As : List Formula)
           -> Eq (allOk P v As) false
           -> Sigma Formula (\ A -> Prod (Mem A As) (Eq (okAt P v A) false))
allOk_false P v []        ()
allOk_false P v (B :: Bs) e =
  sumElim (\ e1 -> sig B (prod memHd e1))
          (\ e2 -> shift (allOk_false P v Bs e2))
          (andFalse (okAt P v B) (allOk P v Bs) e)
  where
    shift : Sigma Formula (\ A -> Prod (Mem A Bs) (Eq (okAt P v A) false))
         -> Sigma Formula (\ A -> Prod (Mem A (B :: Bs)) (Eq (okAt P v A) false))
    shift (sig A (prod m q)) = sig A (prod (memTl m) q)

------------------------------------------------------------------------
-- Searching allCoh

allCoh_at : (P : Formula) (v : Val) (n i : Nat) -> Lt i n
         -> Eq (allCoh P v n) true -> Eq (cohAt P v i) true
allCoh_at P v zero    i ()  e
allCoh_at P v (suc n) i lt  e =
  sumElim (\ eq -> eqSubst (\ k -> Eq (cohAt P v k) true) (eqSym eq)
                           (andTrueL (cohAt P v n) (allCoh P v n) e))
          (\ l  -> allCoh_at P v n i l (andTrueR (cohAt P v n) (allCoh P v n) e))
          (ltSucCase i n lt)

allCoh_false : (P : Formula) (v : Val) (n : Nat)
            -> Eq (allCoh P v n) false
            -> Sigma Nat (\ i -> Prod (Lt i n) (Eq (cohAt P v i) false))
allCoh_false P v zero    ()
allCoh_false P v (suc n) e =
  sumElim (\ e1 -> sig n (prod (ltNSucN n) e1))
          (\ e2 -> shift (allCoh_false P v n e2))
          (andFalse (cohAt P v n) (allCoh P v n) e)
  where
    ltNSucN : (k : Nat) -> Lt k (suc k)
    ltNSucN zero    = ltZero
    ltNSucN (suc k) = ltSuc (ltNSucN k)

    ltWeak : {i k : Nat} -> Lt i k -> Lt i (suc k)
    ltWeak ltZero     = ltZero
    ltWeak (ltSuc l)  = ltSuc (ltWeak l)

    shift : Sigma Nat (\ i -> Prod (Lt i n) (Eq (cohAt P v i) false))
         -> Sigma Nat (\ i -> Prod (Lt i (suc n)) (Eq (cohAt P v i) false))
    shift (sig i (prod l q)) = sig i (prod (ltWeak l) q)

------------------------------------------------------------------------
-- Computational checks.
--
-- dia p is  neg (box (neg p)) , so sub is
--   [ neg (box (neg p)) , box (neg p) , neg p , p ]
-- with no duplicates.  The constraints are v0 = not v1, v1 implies v2,
-- v2 = not v3, leaving three states -- the same three as Example 1 of
-- lecture15.pdf, where Sub(Fp) = {Fp, p} and the excluded combination is
-- Fp false with p true.

diaP : Formula
diaP = dia (var zero)

St_diaP : Eq (length (St diaP)) 3
St_diaP = refl

-- The negation of Ben-Ari's formula, the input the decision procedure is
-- actually run on.  Here sub has length 7 with box p and p each duplicated,
-- so 128 valuations are filtered to 6 states.

negBenAri : Formula
negBenAri = neg benAri

St_negBenAri : Eq (length (allVecs (length (sub negBenAri)))) 128
St_negBenAri = refl

St_negBenAri_count : Eq (length (St negBenAri)) 6
St_negBenAri_count = refl

-- The duplicate-incoherent valuation of LTL.Val is rejected, as intended.

badVal_rejected : Eq (isState benAri badVal) false
badVal_rejected = refl
