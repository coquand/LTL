{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Step -- G6 of FORMALISATION-PLAN.md.
--
-- Definition 2.3 of m4.tex, the transition relation:
--
--   (T1)  for nxt B in Sub(P):  nxt B in v  iff  B in w
--   (T2)  for box A in Sub(P):  box A in v  implies  box A in w
--   (T3)  for box A in Sub(P):  box A not in v and A in v  implies
--                               box A not in w
--
-- (T2) and (T3) are the two halves of  box A <-> A and nxt (box A)  with
-- nxt (box A) read as "box A at the successor"; (S2) of LTL.State is the
-- remaining half.  Keeping them here rather than in the state condition is what
-- lets Sub replace a Fischer-Ladner closure (Remark 2.1), and it also makes
-- persistence (Lemma 2.8) true by definition rather than by proof.

module LTL.Step where

open import LTL.State public

------------------------------------------------------------------------
-- The three conditions, imposed at each member of sub P

stepAt : Formula -> Val -> Val -> Formula -> Bool
stepAt P v w (var n)   = true
stepAt P v w (neg A)   = true
stepAt P v w (imp A B) = true
stepAt P v w (nxt B)   = boolEq (valOf P v (nxt B)) (valOf P w B)
stepAt P v w (box A)   =
  boolAnd (boolImp (valOf P v (box A)) (valOf P w (box A)))
          (boolImp (boolAnd (boolNot (valOf P v (box A))) (valOf P v A))
                   (boolNot (valOf P w (box A))))

allStep : Formula -> Val -> Val -> List Formula -> Bool
allStep P v w []        = true
allStep P v w (A :: As) = boolAnd (stepAt P v w A) (allStep P v w As)

step : Formula -> Val -> Val -> Bool
step P v w = allStep P v w (sub P)

------------------------------------------------------------------------
-- Successors within a given set of states

succs : Formula -> List Val -> Val -> List Val
succs P us v = filterL (step P v) us

------------------------------------------------------------------------
-- Reading one conjunct out of a true step

allStep_at : (P : Formula) (v w : Val) (As : List Formula) {X : Formula}
          -> Mem X As -> Eq (allStep P v w As) true -> Eq (stepAt P v w X) true
allStep_at P v w []        ()        e
allStep_at P v w (B :: Bs) memHd     e =
  andTrueL (stepAt P v w B) (allStep P v w Bs) e
allStep_at P v w (B :: Bs) (memTl m) e =
  allStep_at P v w Bs m (andTrueR (stepAt P v w B) (allStep P v w Bs) e)

------------------------------------------------------------------------
-- Persistence, Lemma 2.8 of m4.tex.
--
-- On paper this needs a line of proof; here it is (T3), read off.

persist : (P : Formula) (v w : Val) (A : Formula)
       -> Mem (box A) (sub P)
       -> Eq (step P v w) true
       -> Eq (valOf P v (box A)) false
       -> Eq (valOf P v A) true
       -> Eq (valOf P w (box A)) false
persist P v w A h st bx a =
  t3aux (valOf P v (box A)) (valOf P v A) (valOf P w (box A))
        (allStep_at P v w (sub P) h st) bx a
  where
    -- x = box A at v,  z = A at v,  y = box A at w
    t3aux : (x z y : Bool)
         -> Eq (boolAnd (boolImp x y)
                        (boolImp (boolAnd (boolNot x) z) (boolNot y))) true
         -> Eq x false -> Eq z true -> Eq y false
    t3aux true  z     y     e () c
    t3aux false false y     e b ()
    t3aux false true  false e b c = refl
    t3aux false true  true  () b c

------------------------------------------------------------------------
-- (T2), read off the same way.
--
-- The note uses it twice: in Lemma 2.7 to refute a successor dropping a box,
-- and in Hintikka's lemma to carry  box A  forward along the run.

carry : (P : Formula) (v w : Val) (A : Formula)
     -> Mem (box A) (sub P)
     -> Eq (step P v w) true
     -> Eq (valOf P v (box A)) true
     -> Eq (valOf P w (box A)) true
carry P v w A h st bx =
  t2aux (valOf P v (box A)) (valOf P v A) (valOf P w (box A))
        (allStep_at P v w (sub P) h st) bx
  where
    t2aux : (x z y : Bool)
         -> Eq (boolAnd (boolImp x y)
                        (boolImp (boolAnd (boolNot x) z) (boolNot y))) true
         -> Eq x true -> Eq y true
    t2aux true  z true  e  b = refl
    t2aux true  z false () b
    t2aux false z y     e  ()

------------------------------------------------------------------------
-- Computational checks.
--
-- For dia p the three states of LTL.State are, writing the bits of
-- [ neg (box (neg p)) , box (neg p) , neg p , p ] :
--
--   s0 = 1 0 0 1   (p holds now)
--   s1 = 1 0 1 0   (p fails now, dia p still pending)
--   s2 = 0 1 1 0   (dia p false, so p fails forever)
--
-- Every state has at least one successor, so no state is removed by (R1).

diaP_succ_counts : Eq (map (\ v -> length (succs diaP (St diaP) v)) (St diaP))
                      (2 :: 3 :: 1 :: [])
diaP_succ_counts = refl

-- For neg benAri the six states are, in the order allVecs produces them
-- (true first, so lexicographic with 1 before 0), writing the bits of
-- [ neg I , I , box p , p , nxt (box p) , box p , p ]  with I = box p -> nxt (box p):
--
--   E = 1 0 1 1 0 1 1     box p true, nxt (box p) false  -- the only state
--                                                        -- containing neg benAri
--   F = 0 1 1 1 1 1 1
--   D = 0 1 0 1 1 0 1
--   C = 0 1 0 1 0 0 1
--   B = 0 1 0 0 1 0 0
--   A = 0 1 0 0 0 0 0
--
-- E and D have NO successor, so both are removed by (R1) alone.

negBenAri_succ_counts
  : Eq (map (\ v -> length (succs negBenAri (St negBenAri) v)) (St negBenAri))
       (0 :: 2 :: 0 :: 4 :: 2 :: 4 :: [])
negBenAri_succ_counts = refl
