{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Skel -- the propositional skeleton of a formula, and the decidable
-- tautology test that (PC) needs.
--
-- Ben-Ari's system (benari.pdf, Definition 12.1) takes as Axiom 0
--
--     PC     any substitution instance of a valid propositional formula
--
-- and then writes "PC" for every propositional step.  m4.tex Remark 6.4 rejects
-- it and uses (P1)-(P3) instead, on the ground that "substitution instance of a
-- propositional tautology" carries a side condition, so a formalisation would
-- have to define a tautology checker AND the substitution relation before it
-- can say what a derivation is, and then prove a substitution lemma to get
-- soundness.
--
-- Half of that objection is avoidable.  The substitution relation is not
-- needed: instead of asking whether A is an instance of a tautology, ask
-- whether A is a tautology OF ITS OWN SKELETON -- treat its var, nxt and box
-- subformulas as atoms and run the truth table.  That is the same class of
-- formulas, it is decidable, it is a boolean condition on A alone, and Deriv
-- stays a plain inductive family.
--
-- The apparatus is already here.  atoms and valFrom were written for G30, where
-- mkV builds a state from an assignment to the atoms of Sub P; the skeleton
-- evaluation is that same function read as a truth-table row.  What this module
-- adds is skelEval, which says the skeleton evaluation agrees with ANY boolean
-- reading of formulas that is compositional on neg and imp -- and there are two
-- such readings in the development, valOf at a state (compositional by (S1))
-- and evalAt at a position (compositional by definition).  So one lemma serves
-- both LTL.Closure and the soundness of (PC).

module LTL.Skel where

open import LTL.Sub public

------------------------------------------------------------------------
-- Valuations, as bit vectors, and their enumeration

Val : Set
Val = List Bool

bitAt : Val -> Nat -> Bool
bitAt v i = nth v i false

allVecs : Nat -> List Val
allVecs zero    = [] :: []
allVecs (suc n) = append (map (\ bs -> true  :: bs) (allVecs n))
                         (map (\ bs -> false :: bs) (allVecs n))

allVecs_complete : (n : Nat) (v : Val) -> Eq (length v) n -> Mem v (allVecs n)
allVecs_complete zero    []            e  = memHd
allVecs_complete zero    (b :: v)      ()
allVecs_complete (suc n) []            ()
allVecs_complete (suc n) (true  :: v)  e  =
  memAppL (map (\ bs -> true :: bs) (allVecs n))
          (map (\ bs -> false :: bs) (allVecs n))
          (memMap (\ bs -> true :: bs) (allVecs_complete n v (sucInj e)))
allVecs_complete (suc n) (false :: v)  e  =
  memAppR (map (\ bs -> true :: bs) (allVecs n))
          (map (\ bs -> false :: bs) (allVecs n))
          (memMap (\ bs -> false :: bs) (allVecs_complete n v (sucInj e)))

------------------------------------------------------------------------
-- Lookup by first occurrence

idxCons : Bool -> Nat -> Nat
idxCons true  n = zero
idxCons false n = suc n

idx : List Formula -> Formula -> Nat
idx []        A = zero
idx (B :: Bs) A = idxCons (formEq B A) (idx Bs A)

------------------------------------------------------------------------
-- Conjunction over a list

allB : {A : Set} -> (A -> Bool) -> List A -> Bool
allB p []        = true
allB p (x :: xs) = boolAnd (p x) (allB p xs)

allB_at : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
       -> Mem x xs -> Eq (allB p xs) true -> Eq (p x) true
allB_at p []        ()        e
allB_at p (y :: ys) memHd     e = andTrueL (p y) (allB p ys) e
allB_at p (y :: ys) (memTl m) e = allB_at p ys m (andTrueR (p y) (allB p ys) e)

allB_intro : {A : Set} (p : A -> Bool) (xs : List A)
          -> ({x : A} -> Mem x xs -> Eq (p x) true) -> Eq (allB p xs) true
allB_intro p []        f = refl
allB_intro p (y :: ys) f =
  andIntro (p y) (allB p ys) (f memHd) (allB_intro p ys (\ m -> f (memTl m)))

------------------------------------------------------------------------
-- Small list infrastructure

eqCong2 : {A B C : Set} (f : A -> B -> C) {x x' : A} {y y' : B}
       -> Eq x x' -> Eq y y' -> Eq (f x y) (f x' y')
eqCong2 f refl refl = refl

map_length : {A B : Set} (f : A -> B) (xs : List A)
          -> Eq (length (map f xs)) (length xs)
map_length f []        = refl
map_length f (x :: xs) = eqCong suc (map_length f xs)

nth_map : {A B : Set} (f : A -> B) (xs : List A) (i : Nat) -> Lt i (length xs)
       -> (d : A) (e : B) -> Eq (nth (map f xs) i e) (f (nth xs i d))
nth_map f []        i       ()        d e
nth_map f (x :: xs) zero    lt        d e = refl
nth_map f (x :: xs) (suc i) (ltSuc l) d e = nth_map f xs i l d e

------------------------------------------------------------------------
-- Formula membership as a boolean, and the idx/nth round-trip for it.
--
-- idx locates the FIRST occurrence of a formula by formEq, so this is the
-- round-trip of FORMALISATION-PLAN.md G2 once more, for lookup by formula
-- rather than by position.

memF : List Formula -> Formula -> Bool
memF []        A = false
memF (B :: Bs) A = boolOr (formEq B A) (memF Bs A)

memF_tail : (B : Formula) (Bs : List Formula) (A : Formula)
         -> Eq (memF (B :: Bs) A) true -> Eq (formEq B A) false
         -> Eq (memF Bs A) true
memF_tail B Bs A e eb =
  sumElim (\ e1 -> emptyElim (tfAbs (eqTrans (eqSym e1) eb)))
          (\ e2 -> e2) (orTrue (formEq B A) (memF Bs A) e)

idxF_nth : (As : List Formula) (A : Formula) -> Eq (memF As A) true
        -> Eq (nth As (idx As A) bot) A
idxF_nth []        A ()
idxF_nth (B :: Bs) A e = go (formEq B A) refl
  where
    go : (b : Bool) -> Eq (formEq B A) b
      -> Eq (nth (B :: Bs) (idxCons b (idx Bs A)) bot) A
    go true  eb = formEq_sound B A eb
    go false eb = idxF_nth Bs A (memF_tail B Bs A e eb)

idxF_lt : (As : List Formula) (A : Formula) -> Eq (memF As A) true
       -> Lt (idx As A) (length As)
idxF_lt []        A ()
idxF_lt (B :: Bs) A e = go (formEq B A) refl
  where
    go : (b : Bool) -> Eq (formEq B A) b
      -> Lt (idxCons b (idx Bs A)) (suc (length Bs))
    go true  eb = ltZero
    go false eb = ltSuc (idxF_lt Bs A (memF_tail B Bs A e eb))

------------------------------------------------------------------------
-- The atoms of a list of formulas.
--
-- Insertion keeps the list free of formEq-duplicates: Sub P repeats (see
-- subBenAri_dup), and a repeated atom would double the truth table for nothing.

isAtomB : Formula -> Bool
isAtomB (var n)   = true
isAtomB (neg A)   = false
isAtomB (imp A B) = false
isAtomB (nxt A)   = true
isAtomB (box A)   = true

insF : Formula -> List Formula -> List Formula
insF A Bs = filterCons (boolNot (memF Bs A)) A Bs

insF_self : (A : Formula) (Bs : List Formula) -> Eq (memF (insF A Bs) A) true
insF_self A Bs = go (memF Bs A) refl
  where
    go : (b : Bool) -> Eq (memF Bs A) b
      -> Eq (memF (filterCons (boolNot b) A Bs) A) true
    go true  e = e
    go false e = orL (formEq A A) (memF Bs A) (formEq_refl A)

insF_mono : (A : Formula) (Bs : List Formula) (X : Formula)
         -> Eq (memF Bs X) true -> Eq (memF (insF A Bs) X) true
insF_mono A Bs X e = go (memF Bs A) refl
  where
    go : (b : Bool) -> Eq (memF Bs A) b
      -> Eq (memF (filterCons (boolNot b) A Bs) X) true
    go true  eb = e
    go false eb = orR (formEq A X) (memF Bs X) e

atoms : List Formula -> List Formula
atoms []              = []
atoms (var n   :: As) = insF (var n) (atoms As)
atoms (neg A   :: As) = atoms As
atoms (imp A B :: As) = atoms As
atoms (nxt A   :: As) = insF (nxt A) (atoms As)
atoms (box A   :: As) = insF (box A) (atoms As)

atomMem : (As : List Formula) {A : Formula} -> Mem A As -> Eq (isAtomB A) true
       -> Eq (memF (atoms As) A) true
atomMem []              ()        e
atomMem (var n   :: As) memHd     e = insF_self (var n) (atoms As)
atomMem (var n   :: As) (memTl m) e = insF_mono (var n) (atoms As) _ (atomMem As m e)
atomMem (neg B   :: As) memHd     ()
atomMem (neg B   :: As) (memTl m) e = atomMem As m e
atomMem (imp B C :: As) memHd     ()
atomMem (imp B C :: As) (memTl m) e = atomMem As m e
atomMem (nxt B   :: As) memHd     e = insF_self (nxt B) (atoms As)
atomMem (nxt B   :: As) (memTl m) e = insF_mono (nxt B) (atoms As) _ (atomMem As m e)
atomMem (box B   :: As) memHd     e = insF_self (box B) (atoms As)
atomMem (box B   :: As) (memTl m) e = insF_mono (box B) (atoms As) _ (atomMem As m e)

------------------------------------------------------------------------
-- The arguments of the box-subformulas.
--
-- boxArgs collects the A for which box A occurs in the list.  It lived in
-- LTL.Elim, which is where the eventualities are; it is here because Phase 9
-- needs it on the OTHER branch of the import graph -- the (S2) premise of the
-- short Lemma 2.6 (LTL.CompletePC) is a conjunction of  box A -> A  over it,
-- and LTL.Complete cannot reach LTL.Elim.  It is a pure syntactic function of
-- a List Formula, so nothing but its position changes; boxArgs_mem stays in
-- LTL.Trace, which is the only place that needs it.

boxArgs : List Formula -> List Formula
boxArgs []              = []
boxArgs (var n   :: As) = boxArgs As
boxArgs (neg A   :: As) = boxArgs As
boxArgs (imp A B :: As) = boxArgs As
boxArgs (nxt A   :: As) = boxArgs As
boxArgs (box A   :: As) = A :: boxArgs As

boxArgs_of : (As : List Formula) {A : Formula}
          -> Mem (box A) As -> Mem A (boxArgs As)
boxArgs_of []                ()
boxArgs_of (var n   :: As) (memTl m) = boxArgs_of As m
boxArgs_of (neg B   :: As) (memTl m) = boxArgs_of As m
boxArgs_of (imp B C :: As) (memTl m) = boxArgs_of As m
boxArgs_of (nxt B   :: As) (memTl m) = boxArgs_of As m
boxArgs_of (box B   :: As) memHd     = memHd
boxArgs_of (box B   :: As) (memTl m) = memTl (boxArgs_of As m)

------------------------------------------------------------------------
-- The skeleton evaluation.
--
-- valFrom Ats a A reads A with the bits a assigned to the atoms Ats: neg and
-- imp are interpreted, everything else is looked up.  For G30 this builds a
-- state out of an assignment; here it is one row of a truth table.

valFrom : List Formula -> Val -> Formula -> Bool
valFrom Ats a (var n)   = bitAt a (idx Ats (var n))
valFrom Ats a (neg A)   = boolNot (valFrom Ats a A)
valFrom Ats a (imp A B) = boolImp (valFrom Ats a A) (valFrom Ats a B)
valFrom Ats a (nxt A)   = bitAt a (idx Ats (nxt A))
valFrom Ats a (box A)   = bitAt a (idx Ats (box A))

------------------------------------------------------------------------
-- The skeleton evaluation agrees with any compositional reading.
--
-- f is an arbitrary assignment of booleans to formulas that respects neg and
-- imp on the subformulas of P.  Then reading A through f is the same as
-- reading it through the skeleton with the atoms interpreted by f.  Two
-- instances are used: valOf at a state, where the hypotheses are (S1) --
-- LTL.Closure -- and evalAt at a position, where they are refl, since evalAt is
-- DEFINED by boolNot and boolImp at neg and imp -- LTL.Sound.

atomLook : (f : Formula -> Bool) (Ats : List Formula) (X : Formula)
        -> Eq (memF Ats X) true
        -> Eq (bitAt (map f Ats) (idx Ats X)) (f X)
atomLook f Ats X mX =
  eqTrans (nth_map f Ats (idx Ats X) (idxF_lt Ats X mX) bot false)
          (eqCong f (idxF_nth Ats X mX))

skelEval : (f : Formula -> Bool) (Ats : List Formula) (P : Formula)
        -> ((X : Formula) -> Mem X (sub P) -> Eq (isAtomB X) true
              -> Eq (memF Ats X) true)
        -> ((X : Formula) -> Mem (neg X) (sub P)
              -> Eq (f (neg X)) (boolNot (f X)))
        -> ((X Y : Formula) -> Mem (imp X Y) (sub P)
              -> Eq (f (imp X Y)) (boolImp (f X) (f Y)))
        -> (A : Formula) -> Mem A (sub P)
        -> Eq (valFrom Ats (map f Ats) A) (f A)
skelEval f Ats P at fn fi (var n)   m = atomLook f Ats (var n) (at (var n) m refl)
skelEval f Ats P at fn fi (nxt A)   m = atomLook f Ats (nxt A) (at (nxt A) m refl)
skelEval f Ats P at fn fi (box A)   m = atomLook f Ats (box A) (at (box A) m refl)
skelEval f Ats P at fn fi (neg A)   m =
  eqTrans (eqCong boolNot (skelEval f Ats P at fn fi A (sub_neg P m)))
          (eqSym (fn A m))
skelEval f Ats P at fn fi (imp A B) m =
  eqTrans (eqCong2 boolImp (skelEval f Ats P at fn fi A (sub_impL P m))
                           (skelEval f Ats P at fn fi B (sub_impR P m)))
          (eqSym (fi A B m))

------------------------------------------------------------------------
-- (PC), as a decidable condition on A alone

atomsOf : Formula -> List Formula
atomsOf A = atoms (sub A)

isTaut : Formula -> Bool
isTaut A = allB (\ a -> valFrom (atomsOf A) a A)
                (allVecs (length (atomsOf A)))

-- and its soundness: any compositional reading of a skeleton tautology is true

tautSound : (f : Formula -> Bool) (A : Formula)
         -> ((X : Formula) -> Mem (neg X) (sub A)
               -> Eq (f (neg X)) (boolNot (f X)))
         -> ((X Y : Formula) -> Mem (imp X Y) (sub A)
               -> Eq (f (imp X Y)) (boolImp (f X) (f Y)))
         -> Eq (isTaut A) true -> Eq (f A) true
tautSound f A fn fi e =
  eqTrans (eqSym (skelEval f (atomsOf A) A
                           (\ X mX aX -> atomMem (sub A) mX aX) fn fi A
                           (sub_self A)))
          (allB_at (\ a -> valFrom (atomsOf A) a A)
                   (allVecs (length (atomsOf A)))
                   (allVecs_complete (length (atomsOf A)) (map f (atomsOf A))
                                     (map_length f (atomsOf A)))
                   e)
