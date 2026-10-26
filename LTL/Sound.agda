{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Sound -- G26 of FORMALISATION-PLAN.md.
--
--   "One checks by induction on derivations that |- C implies [[C]]_s = 1 at
--    every state of every lasso."                          -- m4.tex section 5
--
-- Ten constructors.  Six are Boolean tautologies of at most three variables,
-- written out by cases; (K nxt) and (Lin) reduce to  boolImp z z  because
-- evalAt commutes with nxt definitionally, both sides of (Lin) being
-- boolNot (evalAt A (nextPos pos)) on the nose.  That leaves four.
--
--   (K box)  is allB pointwise: the SAME orbit on both sides, so it is
--            allB_at then impTrueB then allB_intro.
--
--   (Exp)    needs the orbit of pos to contain pos, its successor, and the
--            whole orbit of its successor.  All three are orbitIter, since
--            posIter 0, posIter 1 and posIter (suc t) all land in it.
--
--   (Ind)    is the only one with content, and it is the risk that section 3
--            of the plan ranked fourth.  Under  box (A -> nxt A)  and A at pos,
--            A holds at posIter t pos by induction on t -- the hypothesis is
--            available at posIter t pos because orbitIter puts it in the orbit
--            -- and every member of the orbit is a posIter t pos by
--            orbitOf_iter.  Twenty lines, no arithmetic.
--
--   (gen)    needs every position of an orbit to be VALID, so that the
--            induction hypothesis applies there.  That is orbitValid.
--
-- The evaluation is total on all formulas, not only on subformulas of P, which
-- is what lets this be stated for an arbitrary derivable C.

module LTL.Sound where

open import LTL.Eval public

------------------------------------------------------------------------
-- The Boolean tautologies behind (P1), (P2), (P3) and the identity

tp1 : (a b : Bool) -> Eq (boolImp a (boolImp b a)) true
tp1 true  true  = refl
tp1 true  false = refl
tp1 false b     = refl

tp2 : (a b c : Bool)
   -> Eq (boolImp (boolImp a (boolImp b c))
                  (boolImp (boolImp a b) (boolImp a c))) true
tp2 true  true  true  = refl
tp2 true  true  false = refl
tp2 true  false true  = refl
tp2 true  false false = refl
tp2 false b     c     = refl

tp3 : (a b : Bool)
   -> Eq (boolImp (boolImp (boolNot b) (boolNot a)) (boolImp a b)) true
tp3 true  true  = refl
tp3 true  false = refl
tp3 false true  = refl
tp3 false false = refl

tid : (a : Bool) -> Eq (boolImp a a) true
tid true  = refl
tid false = refl

------------------------------------------------------------------------
-- Conjunction, as (Exp) and (Lin) need it

conTrue : (P : Formula) (c0 : Val) (c1 : List Val) (X Y : Formula) (pos : Pos)
       -> Eq (evalAt P c0 c1 X pos) true -> Eq (evalAt P c0 c1 Y pos) true
       -> Eq (evalAt P c0 c1 (con X Y) pos) true
conTrue P c0 c1 X Y pos ex ey =
  aux (evalAt P c0 c1 X pos) (evalAt P c0 c1 Y pos) ex ey
  where
    aux : (x y : Bool) -> Eq x true -> Eq y true
       -> Eq (boolNot (boolImp x (boolNot y))) true
    aux true  true  ex' ey' = refl
    aux true  false ex' ()
    aux false y     ()  ey'

------------------------------------------------------------------------
-- (K box)

boxK : (P : Formula) (c0 : Val) (c1 : List Val) (A B : Formula) (pos : Pos)
    -> Eq (evalAt P c0 c1 (box (imp A B)) pos) true
    -> Eq (evalAt P c0 c1 (box A) pos) true
    -> Eq (evalAt P c0 c1 (box B) pos) true
boxK P c0 c1 A B pos e1 e2 =
  allB_intro (evalAt P c0 c1 B) (orbitOf c0 c1 pos)
    (\ {q} m -> impTrueB (evalAt P c0 c1 A q) (evalAt P c0 c1 B q)
                         (allB_at (evalAt P c0 c1 (imp A B)) (orbitOf c0 c1 pos) m e1)
                         (allB_at (evalAt P c0 c1 A) (orbitOf c0 c1 pos) m e2))

------------------------------------------------------------------------
-- (Exp)

expSound : (P : Formula) (c0 : Val) (c1 : List Val) (A : Formula) (pos : Pos)
        -> Eq (evalAt P c0 c1 (imp (box A) (con A (con (nxt A) (nxt (box A))))) pos)
              true
expSound P c0 c1 A pos =
  impIntroB (evalAt P c0 c1 (box A) pos)
            (evalAt P c0 c1 (con A (con (nxt A) (nxt (box A)))) pos) body
  where
    body : Eq (evalAt P c0 c1 (box A) pos) true
        -> Eq (evalAt P c0 c1 (con A (con (nxt A) (nxt (box A)))) pos) true
    body eb =
      conTrue P c0 c1 A (con (nxt A) (nxt (box A))) pos
              (allB_at (evalAt P c0 c1 A) (orbitOf c0 c1 pos)
                       (orbitIter c0 c1 zero pos) eb)
              (conTrue P c0 c1 (nxt A) (nxt (box A)) pos
                       (allB_at (evalAt P c0 c1 A) (orbitOf c0 c1 pos)
                                (orbitIter c0 c1 (suc zero) pos) eb)
                       (allB_intro (evalAt P c0 c1 A)
                                   (orbitOf c0 c1 (nextPos c0 c1 pos))
                                   (\ {q} m ->
                                      allB_at (evalAt P c0 c1 A) (orbitOf c0 c1 pos)
                                              (orbitSub c0 c1 pos q m) eb)))

------------------------------------------------------------------------
-- (Ind).
--
-- The forward induction the note leaves to "one checks": A propagates along
-- the run because the hypothesis is available at every stage of it, and the
-- orbit consists exactly of those stages.

indSound : (P : Formula) (c0 : Val) (c1 : List Val) (A : Formula) (pos : Pos)
        -> Eq (evalAt P c0 c1 (imp (box (imp A (nxt A))) (imp A (box A))) pos) true
indSound P c0 c1 A pos =
  impIntroB (evalAt P c0 c1 (box (imp A (nxt A))) pos)
            (boolImp (evalAt P c0 c1 A pos) (evalAt P c0 c1 (box A) pos))
            (\ e1 -> impIntroB (evalAt P c0 c1 A pos) (evalAt P c0 c1 (box A) pos)
                               (body e1))
  where
    body : Eq (evalAt P c0 c1 (box (imp A (nxt A))) pos) true
        -> Eq (evalAt P c0 c1 A pos) true
        -> Eq (evalAt P c0 c1 (box A) pos) true
    body e1 e2 =
      allB_intro (evalAt P c0 c1 A) (orbitOf c0 c1 pos)
                 (\ {q} m -> fromIter q (orbitOf_iter c0 c1 pos q m))
      where
        along : (t : Nat) -> Eq (evalAt P c0 c1 A (posIter c0 c1 t pos)) true
        along zero    = e2
        along (suc t) =
          eqSubst (\ r -> Eq (evalAt P c0 c1 A r) true)
                  (eqSym (posIter_suc c0 c1 t pos))
                  (impTrueB (evalAt P c0 c1 A (posIter c0 c1 t pos))
                            (evalAt P c0 c1 A
                                    (nextPos c0 c1 (posIter c0 c1 t pos)))
                            (allB_at (evalAt P c0 c1 (imp A (nxt A)))
                                     (orbitOf c0 c1 pos)
                                     (orbitIter c0 c1 t pos) e1)
                            (along t))

        fromIter : (q : Pos) -> Sigma Nat (\ t -> Eq (posIter c0 c1 t pos) q)
                -> Eq (evalAt P c0 c1 A q) true
        fromIter q (sig t et) =
          eqSubst (\ r -> Eq (evalAt P c0 c1 A r) true) et (along t)

------------------------------------------------------------------------
-- Soundness

sound : (P : Formula) (b c0 : Val) (c1 : List Val)
     -> Mem c0 (Uinf P) -> Walk P (Uinf P) c0 c1 b -> Eq (step P b c0) true
     -> {C : Formula} -> Deriv C
     -> (pos : Pos) -> ValidPos P b pos
     -> Eq (evalAt P c0 c1 C pos) true

sound P b c0 c1 mc0 wc stb (p1 {A} {B}) pos vp =
  tp1 (evalAt P c0 c1 A pos) (evalAt P c0 c1 B pos)

sound P b c0 c1 mc0 wc stb (p2 {A} {B} {C}) pos vp =
  tp2 (evalAt P c0 c1 A pos) (evalAt P c0 c1 B pos) (evalAt P c0 c1 C pos)

sound P b c0 c1 mc0 wc stb (p3 {A} {B}) pos vp =
  tp3 (evalAt P c0 c1 A pos) (evalAt P c0 c1 B pos)

sound P b c0 c1 mc0 wc stb (kbox {A} {B}) pos vp =
  impIntroB (evalAt P c0 c1 (box (imp A B)) pos)
            (boolImp (evalAt P c0 c1 (box A) pos) (evalAt P c0 c1 (box B) pos))
            (\ e1 -> impIntroB (evalAt P c0 c1 (box A) pos)
                               (evalAt P c0 c1 (box B) pos)
                               (\ e2 -> boxK P c0 c1 A B pos e1 e2))

-- both sides are boolImp (evalAt A (nextPos pos)) (evalAt B (nextPos pos))
sound P b c0 c1 mc0 wc stb (knxt {A} {B}) pos vp =
  tid (boolImp (evalAt P c0 c1 A (nextPos c0 c1 pos))
               (evalAt P c0 c1 B (nextPos c0 c1 pos)))

sound P b c0 c1 mc0 wc stb (exp {A}) pos vp = expSound P c0 c1 A pos

sound P b c0 c1 mc0 wc stb (ind {A}) pos vp = indSound P c0 c1 A pos

-- nxt (neg A) and neg (nxt A) evaluate to the same Boolean, so both halves of
-- the biconditional are boolImp z z
sound P b c0 c1 mc0 wc stb (lin {A}) pos vp =
  conTrue P c0 c1 (imp (nxt (neg A)) (neg (nxt A)))
                  (imp (neg (nxt A)) (nxt (neg A))) pos
          (tid (boolNot (evalAt P c0 c1 A (nextPos c0 c1 pos))))
          (tid (boolNot (evalAt P c0 c1 A (nextPos c0 c1 pos))))

-- (PC).  evalAt is DEFINED by boolNot at neg and by boolImp at imp, so the two
-- compositionality hypotheses of tautSound are refl and the case is one line.
-- This is the whole of Ben-Ari's Axiom 0, and it is where the substitution
-- lemma that Remark 6.4 feared would have gone.
sound P b c0 c1 mc0 wc stb (pc {C} e) pos vp =
  tautSound (\ X -> evalAt P c0 c1 X pos) C (\ X m -> refl) (\ X Y m -> refl) e

sound P b c0 c1 mc0 wc stb (mp {A} {B} d e) pos vp =
  impTrueB (evalAt P c0 c1 A pos) (evalAt P c0 c1 B pos)
           (sound P b c0 c1 mc0 wc stb d pos vp)
           (sound P b c0 c1 mc0 wc stb e pos vp)

sound P b c0 c1 mc0 wc stb (gen {A} d) pos vp =
  allB_intro (evalAt P c0 c1 A) (orbitOf c0 c1 pos)
             (\ {q} m -> sound P b c0 c1 mc0 wc stb d q
                               (orbitValid P b c0 c1 mc0 wc stb pos q vp m))

------------------------------------------------------------------------
-- Soundness on a run, at every stage

soundRun : (P : Formula) (v0 : Val) (r : Run P v0) {C : Formula} -> Deriv C
        -> (i : Nat) -> Eq (eval P v0 r C i) true
soundRun P v0 (mkRun b c0 c1 mc0 wc stb mbc cyc rest mv0 wr) d i =
  sound P b c0 c1 mc0 wc stb d
        (posIter c0 c1 i (prod v0 rest))
        (posIterValid P b c0 c1 mc0 wc stb i (prod v0 rest) (vpos v0 rest mv0 wr))
