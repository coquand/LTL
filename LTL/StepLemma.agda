{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.StepLemma -- G18 and G19 of FORMALISATION-PLAN.md,
-- Lemmas 2.7 and 2.8 of m4.tex.
--
--   stepLemma : Deriv (imp (chi P v) (nxt (beta P (succs P (St P) v))))
--
-- Following the note: state completeness and (D1) give |- nxt (beta St),
-- hence a disjunction of nxt chi_w by (D4); the w with v not-> w are dropped;
-- (D4) carries the survivors back under a single nxt.
--
-- The four refutation cases are done with the CONJUNCTION as antecedent,
--   R = con (chi P v) (nxt (chi P w)) ,
-- deriving  Deriv (neg R)  and converting at the end by dne.  That keeps every
-- case at one antecedent level, where conFst and conSnd give both halves.
--
-- G19 (persistence, Lemma 2.8) is already discharged in LTL.Step as `persist`;
-- it is (T3) read off, so nothing is added here.

module LTL.StepLemma where

open import LTL.Complete public
open import LTL.Step     public

------------------------------------------------------------------------
-- Searching a false allStep

allStep_false : (P : Formula) (v w : Val) (As : List Formula)
             -> Eq (allStep P v w As) false
             -> Sigma Formula (\ A -> Prod (Mem A As) (Eq (stepAt P v w A) false))
allStep_false P v w []        ()
allStep_false P v w (B :: Bs) e =
  sumElim (\ e1 -> sig B (prod memHd e1))
          (\ e2 -> shift (allStep_false P v w Bs e2))
          (andFalse (stepAt P v w B) (allStep P v w Bs) e)
  where
    shift : Sigma Formula (\ A -> Prod (Mem A Bs) (Eq (stepAt P v w A) false))
         -> Sigma Formula (\ A -> Prod (Mem A (B :: Bs)) (Eq (stepAt P v w A) false))
    shift (sig A (prod m q)) = sig A (prod (memTl m) q)

------------------------------------------------------------------------
-- Closing the (T1) case, uniformly in the bit

refuteNxt : {R B : Formula} (c : Bool)
         -> Deriv (imp R (lit (nxt B) (boolNot c)))
         -> Deriv (imp R (nxt (lit B c)))
         -> Deriv (neg R)
refuteNxt true  f g = refute g f
refuteNxt false f g = refute f (impTrans g linF)

------------------------------------------------------------------------
-- Refuting a non-successor

notSucc : (P : Formula) (v w : Val)
       -> Eq (length v) (length (sub P))
       -> Eq (length w) (length (sub P))
       -> Eq (step P v w) false
       -> Deriv (neg (con (chi P v) (nxt (chi P w))))
notSucc P v w lenv lenw e = sigElim (allStep_false P v w (sub P) e)
  where
    R : Formula
    R = con (chi P v) (nxt (chi P w))

    pv : {A : Formula} -> Mem A (sub P) -> Deriv (imp R (lit A (valOf P v A)))
    pv m = impTrans conFst (chiProjVal P v lenv m)

    pw : {A : Formula} -> Mem A (sub P) -> Deriv (imp R (nxt (lit A (valOf P w A))))
    pw m = impTrans conSnd (nxtMono (chiProjVal P w lenw m))

    pvAt : {A : Formula} -> Mem A (sub P) -> (c : Bool) -> Eq (valOf P v A) c
        -> Deriv (imp R (lit A c))
    pvAt m c eq = eqSubst (\ d -> Deriv (imp R (lit _ d))) eq (pv m)

    pwAt : {A : Formula} -> Mem A (sub P) -> (c : Bool) -> Eq (valOf P w A) c
        -> Deriv (imp R (nxt (lit A c)))
    pwAt m c eq = eqSubst (\ d -> Deriv (imp R (nxt (lit _ d)))) eq (pw m)

    ----------------------------------------------------------------
    -- (T1)

    caseNxt : {B : Formula} -> Mem (nxt B) (sub P)
           -> Eq (boolEq (valOf P v (nxt B)) (valOf P w B)) false
           -> Deriv (neg R)
    caseNxt {B} m q =
      refuteNxt (valOf P w B)
                (pvAt m (boolNot (valOf P w B))
                      (boolEq_false_eq (valOf P v (nxt B)) (valOf P w B) q))
                (pwAt (sub_nxt P m) (valOf P w B) refl)

    ----------------------------------------------------------------
    -- (T2) and (T3)

    caseBox : {B : Formula} -> Mem (box B) (sub P)
           -> Eq (boolAnd (boolImp (valOf P v (box B)) (valOf P w (box B)))
                          (boolImp (boolAnd (boolNot (valOf P v (box B)))
                                            (valOf P v B))
                                   (boolNot (valOf P w (box B))))) false
           -> Deriv (neg R)
    caseBox {B} m q = sumElim t2 t3 (andFalse _ _ q)
      where
        -- (T2): box B holds at v, so it must hold at w; it does not.
        t2 : Eq (boolImp (valOf P v (box B)) (valOf P w (box B))) false
          -> Deriv (neg R)
        t2 q2 = refute (impTrans (pvAt m true (prodFst pr)) boxNxtBox)
                       (impTrans (pwAt m false (prodSnd pr)) linF)
          where
            pr : Prod (Eq (valOf P v (box B)) true) (Eq (valOf P w (box B)) false)
            pr = boolImp_false (valOf P v (box B)) (valOf P w (box B)) q2

        -- (T3): box B fails at v while B holds, so box B must fail at w;
        -- it holds, and (D6) turns B with nxt (box B) back into box B.
        t3 : Eq (boolImp (boolAnd (boolNot (valOf P v (box B))) (valOf P v B))
                         (boolNot (valOf P w (box B)))) false
          -> Deriv (neg R)
        t3 q3 = refute (impTrans (conPair (pvAt (sub_box P m) true eB)
                                          (pwAt m true eW))
                                 expConv)
                       (pvAt m false eV)
          where
            pr : Prod (Eq (boolAnd (boolNot (valOf P v (box B))) (valOf P v B)) true)
                      (Eq (boolNot (valOf P w (box B))) false)
            pr = boolImp_false _ _ q3

            eV : Eq (valOf P v (box B)) false
            eV = notTrue (valOf P v (box B))
                         (andTrueL (boolNot (valOf P v (box B))) (valOf P v B)
                                   (prodFst pr))
              where
                notTrue : (b : Bool) -> Eq (boolNot b) true -> Eq b false
                notTrue true  ()
                notTrue false e' = refl

            eB : Eq (valOf P v B) true
            eB = andTrueR (boolNot (valOf P v (box B))) (valOf P v B) (prodFst pr)

            eW : Eq (valOf P w (box B)) true
            eW = notFalse (valOf P w (box B)) (prodSnd pr)
              where
                notFalse : (b : Bool) -> Eq (boolNot b) false -> Eq b true
                notFalse true  e' = refl
                notFalse false ()

    ----------------------------------------------------------------

    byShape : {A : Formula} -> Mem A (sub P) -> Eq (stepAt P v w A) false
           -> Deriv (neg R)
    byShape {var n}   m ()
    byShape {neg B}   m ()
    byShape {imp B D} m ()
    byShape {nxt B}   m q = caseNxt m q
    byShape {box B}   m q = caseBox m q

    sigElim : Sigma Formula (\ A -> Prod (Mem A (sub P))
                                         (Eq (stepAt P v w A) false))
           -> Deriv (neg R)
    sigElim (sig A (prod m q)) = byShape m q

badSucc : (P : Formula) (v w : Val)
       -> Eq (length v) (length (sub P))
       -> Eq (length w) (length (sub P))
       -> Eq (step P v w) false
       -> Deriv (imp (chi P v) (neg (nxt (chi P w))))
badSucc P v w lenv lenw e = mp dne (notSucc P v w lenv lenw e)

------------------------------------------------------------------------
-- Dropping the non-successors under the antecedent chi P v

allLen_filter : {n : Nat} (p : Val -> Bool) {vs : List Val}
             -> AllLen n vs -> AllLen n (filterL p vs)
allLen_filter p alNil                 = alNil
allLen_filter p {v :: vs} (alCons e al) = aux (p v)
  where
    aux : (b : Bool) -> AllLen _ (filterCons b v (filterL p vs))
    aux true  = alCons e (allLen_filter p al)
    aux false = allLen_filter p al

map_filterCons2 : (P : Formula) (b : Bool) (w : Val) (L : List Val)
               -> Eq (map nxt (map (chi P) (filterCons b w L)))
                     (filterCons b (nxt (chi P w)) (map nxt (map (chi P) L)))
map_filterCons2 P true  w L = refl
map_filterCons2 P false w L = refl

filterImp : (P : Formula) (v : Val) (Q : Formula) (ws : List Val)
         -> AllLen (length (sub P)) ws
         -> ((w : Val) -> Eq (length w) (length (sub P)) -> Eq (step P v w) false
               -> Deriv (imp Q (neg (nxt (chi P w)))))
         -> Deriv (imp Q (imp (disj (map nxt (map (chi P) ws)))
                              (disj (map nxt (map (chi P)
                                       (filterL (step P v) ws))))))
filterImp P v Q []        alNil           bad = liftP impRefl
filterImp P v Q (w :: ws) (alCons lenw al) bad =
  eqSubst (\ L -> Deriv (imp Q (imp (disj (nxt (chi P w)
                                            :: map nxt (map (chi P) ws)))
                                    (disj L))))
          (eqSym (map_filterCons2 P (step P v w) w (filterL (step P v) ws)))
          (onStep (step P v w) refl)
  where
    ih : Deriv (imp Q (imp (disj (map nxt (map (chi P) ws)))
                           (disj (map nxt (map (chi P) (filterL (step P v) ws))))))
    ih = filterImp P v Q ws al bad

    X : Formula
    X = nxt (chi P w)

    onStep : (b : Bool) -> Eq (step P v w) b
          -> Deriv (imp Q (imp (disj (X :: map nxt (map (chi P) ws)))
                               (disj (filterCons b X
                                       (map nxt (map (chi P)
                                          (filterL (step P v) ws)))))))
    -- kept: compose under the same antecedent neg X
    onStep true  e = mpU (liftP p2) (impTrans ih p1)
    -- dropped: neg X is available, so the antecedent neg X can be discharged
    onStep false e =
      impTransU (impTrans (bad w lenw e) (impSwap impRefl)) ih

------------------------------------------------------------------------
-- Lemma 2.7

stepLemma : (P : Formula) (v : Val)
         -> Eq (length v) (length (sub P))
         -> Deriv (imp (chi P v) (nxt (beta P (succs P (St P) v))))
stepLemma P v lenv =
  impTrans (mpU (filterImp P v (chi P v) (St P) stLen bad) start)
           (nxtDisjL2 (map (chi P) (succs P (St P) v)))
  where
    stLen : AllLen (length (sub P)) (St P)
    stLen = allLen_filter (isState P) (allVecs_allLen (length (sub P)))

    bad : (w : Val) -> Eq (length w) (length (sub P)) -> Eq (step P v w) false
       -> Deriv (imp (chi P v) (neg (nxt (chi P w))))
    bad w lenw e = badSucc P v w lenv lenw e

    start : Deriv (imp (chi P v) (disj (map nxt (map (chi P) (St P)))))
    start = liftP (mp (nxtDisjL1 (map (chi P) (St P)))
                      (nxtGen (stateComplete P)))
