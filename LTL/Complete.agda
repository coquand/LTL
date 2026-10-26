{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Complete -- G17 of FORMALISATION-PLAN.md, Lemma 2.6 of m4.tex.
--
--   stateComplete : Deriv (beta P (St P))
--
-- Two steps.  First the disjunction over ALL valuations, by structural
-- induction along sub P: each step splits on the next formula with splitD
-- (L6).  Then the non-states are dropped by disjDrop, using nonState (G16).
--
-- The work is in lining up the shapes: allVecs (suc n) is built by consing
-- true and false onto allVecs n and appending, while splitOn conjoins A and
-- neg A onto a list of formulas and appends.  stepEq says these agree once
-- chi is applied, and it holds because  conj (litList (A :: As) (b :: w))
-- reduces to  con (lit A b) (conj (litList As w)).

module LTL.Complete where

open import LTL.NonState public

------------------------------------------------------------------------
-- chi against an arbitrary list of formulas

chiOf : List Formula -> Val -> Formula
chiOf As v = conj (litList As v)

------------------------------------------------------------------------
-- Lining up allVecs with splitOn

appCong : {A : Set} {xs xs' ys ys' : List A}
       -> Eq xs xs' -> Eq ys ys' -> Eq (append xs ys) (append xs' ys')
appCong refl refl = refl

lemTrue : (A : Formula) (As : List Formula) (V : List Val)
       -> Eq (map (chiOf (A :: As)) (map (\ w -> true :: w) V))
             (map (con A) (map (chiOf As) V))
lemTrue A As V = eqTrans (map_map (chiOf (A :: As)) (\ w -> true :: w) V)
                         (eqSym (map_map (con A) (chiOf As) V))

lemFalse : (A : Formula) (As : List Formula) (V : List Val)
        -> Eq (map (chiOf (A :: As)) (map (\ w -> false :: w) V))
              (map (con (neg A)) (map (chiOf As) V))
lemFalse A As V = eqTrans (map_map (chiOf (A :: As)) (\ w -> false :: w) V)
                          (eqSym (map_map (con (neg A)) (chiOf As) V))

stepEq : (A : Formula) (As : List Formula)
      -> Eq (map (chiOf (A :: As)) (allVecs (suc (length As))))
            (splitOn A (map (chiOf As) (allVecs (length As))))
stepEq A As =
  eqTrans (map_append (chiOf (A :: As))
                      (map (\ w -> true  :: w) (allVecs (length As)))
                      (map (\ w -> false :: w) (allVecs (length As))))
          (appCong (lemTrue  A As (allVecs (length As)))
                   (lemFalse A As (allVecs (length As))))

------------------------------------------------------------------------
-- The disjunction over all valuations

allComplete : (As : List Formula)
           -> Deriv (disj (map (chiOf As) (allVecs (length As))))
allComplete []        = mp (disjIntro (top :: []) memHd) derivTop
allComplete (A :: As) =
  eqSubst (\ L -> Deriv (disj L)) (eqSym (stepEq A As))
          (splitD (map (chiOf As) (allVecs (length As))) (allComplete As))

------------------------------------------------------------------------
-- Every vector produced by allVecs n has length n

data AllLen (n : Nat) : List Val -> Set where
  alNil  : AllLen n []
  alCons : {v : Val} {vs : List Val}
        -> Eq (length v) n -> AllLen n vs -> AllLen n (v :: vs)

allLen_append : {n : Nat} {xs ys : List Val}
             -> AllLen n xs -> AllLen n ys -> AllLen n (append xs ys)
allLen_append alNil          ay = ay
allLen_append (alCons e ax)  ay = alCons e (allLen_append ax ay)

allLen_cons : (b : Bool) {n : Nat} {V : List Val}
           -> AllLen n V -> AllLen (suc n) (map (\ w -> b :: w) V)
allLen_cons b alNil         = alNil
allLen_cons b (alCons e ax) = alCons (eqCong suc e) (allLen_cons b ax)

allVecs_allLen : (n : Nat) -> AllLen n (allVecs n)
allVecs_allLen zero    = alCons refl alNil
allVecs_allLen (suc n) =
  allLen_append (allLen_cons true  (allVecs_allLen n))
                (allLen_cons false (allVecs_allLen n))

------------------------------------------------------------------------
-- Dropping the non-states

map_filterCons : (P : Formula) (b : Bool) (v : Val) (L : List Val)
              -> Eq (map (chi P) (filterCons b v L))
                    (filterCons b (chi P v) (map (chi P) L))
map_filterCons P true  v L = refl
map_filterCons P false v L = refl

disjFilter : (P : Formula) (vs : List Val)
          -> AllLen (length (sub P)) vs
          -> Deriv (imp (disj (map (chi P) vs))
                        (disj (map (chi P) (filterL (isState P) vs))))
disjFilter P []        alNil          = impRefl
disjFilter P (v :: vs) (alCons len al) =
  eqSubst (\ L -> Deriv (imp (disj (chi P v :: map (chi P) vs)) (disj L)))
          (eqSym (map_filterCons P (isState P v) v (filterL (isState P) vs)))
          (onState (isState P v) refl)
  where
    ih : Deriv (imp (disj (map (chi P) vs))
                    (disj (map (chi P) (filterL (isState P) vs))))
    ih = disjFilter P vs al

    onState : (b : Bool) -> Eq (isState P v) b
           -> Deriv (imp (disj (chi P v :: map (chi P) vs))
                         (disj (filterCons b (chi P v)
                                 (map (chi P) (filterL (isState P) vs)))))
    onState true  e = disMonoR ih
    onState false e =
      impTrans (disjDrop (map (chi P) vs) (nonState P v len e)) ih

------------------------------------------------------------------------
-- Lemma 2.6

stateComplete : (P : Formula) -> Deriv (beta P (St P))
stateComplete P =
  mp (disjFilter P (allVecs (length (sub P)))
                 (allVecs_allLen (length (sub P))))
     (allComplete (sub P))
