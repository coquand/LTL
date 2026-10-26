{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Hintikka -- G27 of FORMALISATION-PLAN.md.
--
--   "and by induction on formulas, using (T1) for Next, (S2) and (T2) for
--    Always A in v_i, and Lemma 5.4 for Always A not in v_i, that
--    A in v_i  iff  [[A]]_{v_i} = 1   (A in Sub(phi)),
--    which is Hintikka's lemma."                           -- m4.tex section 5
--
-- Stated as an equality of Booleans rather than as a biconditional, which is
-- the same thing here and saves carrying two implications through five cases:
--
--   valOf P (state at pos) A  =  evalAt P c0 c1 A pos       for A in Sub(P).
--
-- The five cases are the note's, one apparatus each:
--
--   var       nothing to do -- evalAt reads the state through valOf.
--   neg, imp  (S1), through okAt at a state of U_inf.
--   nxt       (T1), through allStep_at at the transition posStep supplies.
--   box       both halves.  If box A is in the state, (T2) carries it along the
--             run -- boxAlong -- and (S2) turns it into A at each stage, and
--             every position of the orbit is such a stage.  If box A is not in
--             the state, Lemma 5.4 hands over a position of the orbit at which
--             A fails, and one false conjunct refutes the conjunction.
--
-- Both halves of the box case use exactly one lemma each from Phase 6: carry
-- (T2) and globalFulfil (G24).  Nothing else in the development is needed.

module LTL.Hintikka where

open import LTL.Sound   public
open import LTL.Extract public

------------------------------------------------------------------------
-- Reading (S1) and (S2) off a survivor

stateOk : (P : Formula) (s : Val) -> Mem s (Uinf P) -> {A : Formula}
       -> Mem A (sub P) -> Eq (okAt P s A) true
stateOk P s m mA =
  allOk_at P s (sub P) mA
           (andTrueL (allOk P s (sub P)) (allCoh P s (length (sub P)))
                     (uinfState P s m))

-- (S2)
boxS2 : (P : Formula) (s : Val) -> Mem s (Uinf P) -> (B : Formula)
     -> Mem (box B) (sub P) -> Eq (valOf P s (box B)) true -> Eq (valOf P s B) true
boxS2 P s m B mb e =
  impTrueB (valOf P s (box B)) (valOf P s B) (stateOk P s m mb) e

impCong : {a a' b b' : Bool} -> Eq a a' -> Eq b b'
       -> Eq (boolImp a b) (boolImp a' b')
impCong refl refl = refl

------------------------------------------------------------------------
-- (T2) along the run, and its consequence at every position of an orbit

boxAlong : (P : Formula) (b c0 : Val) (c1 : List Val)
        -> Mem c0 (Uinf P) -> Walk P (Uinf P) c0 c1 b -> Eq (step P b c0) true
        -> (B : Formula) -> Mem (box B) (sub P)
        -> (t : Nat) (pos : Pos) -> ValidPos P b pos
        -> Eq (valOf P (posState pos) (box B)) true
        -> Eq (valOf P (posState (posIter c0 c1 t pos)) (box B)) true
boxAlong P b c0 c1 mc0 wc stb B mb zero    pos vp e = e
boxAlong P b c0 c1 mc0 wc stb B mb (suc t) pos vp e =
  boxAlong P b c0 c1 mc0 wc stb B mb t (nextPos c0 c1 pos)
           (prodFst (posStep P b c0 c1 mc0 wc stb vp))
           (carry P (posState pos) (posState (nextPos c0 c1 pos)) B mb
                  (prodSnd (posStep P b c0 c1 mc0 wc stb vp)) e)

boxTrue : (P : Formula) (b c0 : Val) (c1 : List Val)
       -> Mem c0 (Uinf P) -> Walk P (Uinf P) c0 c1 b -> Eq (step P b c0) true
       -> (B : Formula) -> Mem (box B) (sub P)
       -> (pos q : Pos) -> ValidPos P b pos -> Mem q (orbitOf c0 c1 pos)
       -> Eq (valOf P (posState pos) (box B)) true
       -> Eq (valOf P (posState q) B) true
boxTrue P b c0 c1 mc0 wc stb B mb pos q vp m e =
  fromIter (orbitOf_iter c0 c1 pos q m)
  where
    fromIter : Sigma Nat (\ t -> Eq (posIter c0 c1 t pos) q)
            -> Eq (valOf P (posState q) B) true
    fromIter (sig t et) =
      eqSubst (\ r -> Eq (valOf P (posState r) B) true) et
              (boxS2 P (posState (posIter c0 c1 t pos))
                     (posIn P b (posIterValid P b c0 c1 mc0 wc stb t pos vp))
                     B mb (boxAlong P b c0 c1 mc0 wc stb B mb t pos vp e))

------------------------------------------------------------------------
-- Hintikka's lemma

hint : (P : Formula) (b c0 : Val) (c1 : List Val)
    -> Mem c0 (Uinf P) -> Walk P (Uinf P) c0 c1 b -> Eq (step P b c0) true
    -> Mem b (c0 :: c1)
    -> ((s : Val) -> Mem s (b :: c0 :: c1)
          -> (A : Formula) -> Mem A (boxArgs (sub P))
          -> Eq (valOf P s (box A)) false -> Fulfil P A b (c0 :: c1))
    -> (A : Formula) -> Mem A (sub P)
    -> (pos : Pos) -> ValidPos P b pos
    -> Eq (valOf P (posState pos) A) (evalAt P c0 c1 A pos)

hint P b c0 c1 mc0 wc stb mbc cyc (var n) mA pos vp = refl

hint P b c0 c1 mc0 wc stb mbc cyc (neg B) mA pos vp =
  eqTrans (boolEq_sound (valOf P (posState pos) (neg B))
                        (boolNot (valOf P (posState pos) B))
                        (stateOk P (posState pos) (posIn P b vp) mA))
          (eqCong boolNot
                  (hint P b c0 c1 mc0 wc stb mbc cyc B (sub_neg P mA) pos vp))

hint P b c0 c1 mc0 wc stb mbc cyc (imp B C) mA pos vp =
  eqTrans (boolEq_sound (valOf P (posState pos) (imp B C))
                        (boolImp (valOf P (posState pos) B)
                                 (valOf P (posState pos) C))
                        (stateOk P (posState pos) (posIn P b vp) mA))
          (impCong (hint P b c0 c1 mc0 wc stb mbc cyc B (sub_impL P mA) pos vp)
                   (hint P b c0 c1 mc0 wc stb mbc cyc C (sub_impR P mA) pos vp))

hint P b c0 c1 mc0 wc stb mbc cyc (nxt B) mA pos vp =
  eqTrans (boolEq_sound (valOf P (posState pos) (nxt B))
                        (valOf P (posState (nextPos c0 c1 pos)) B)
                        (allStep_at P (posState pos)
                                    (posState (nextPos c0 c1 pos)) (sub P) mA
                                    (prodSnd (posStep P b c0 c1 mc0 wc stb vp))))
          (hint P b c0 c1 mc0 wc stb mbc cyc B (sub_nxt P mA)
                (nextPos c0 c1 pos) (prodFst (posStep P b c0 c1 mc0 wc stb vp)))

hint P b c0 c1 mc0 wc stb mbc cyc (box B) mA pos vp =
  onBox (valOf P (posState pos) (box B)) refl
  where
    ih : (q : Pos) -> ValidPos P b q
      -> Eq (valOf P (posState q) B) (evalAt P c0 c1 B q)
    ih q vq = hint P b c0 c1 mc0 wc stb mbc cyc B (sub_box P mA) q vq

    -- box B holds: (T2) carries it, (S2) delivers B at every stage
    allTrue : Eq (valOf P (posState pos) (box B)) true
           -> Eq (evalAt P c0 c1 (box B) pos) true
    allTrue e =
      allB_intro (evalAt P c0 c1 B) (orbitOf c0 c1 pos) (\ {q} m -> atQ q m)
      where
        atQ : (q : Pos) -> Mem q (orbitOf c0 c1 pos) -> Eq (evalAt P c0 c1 B q) true
        atQ q m =
          eqTrans (eqSym (ih q (orbitValid P b c0 c1 mc0 wc stb pos q vp m)))
                  (boxTrue P b c0 c1 mc0 wc stb B mA pos q vp m e)

    -- box B fails: Lemma 5.4 supplies the false conjunct
    allFalse : Eq (valOf P (posState pos) (box B)) false
            -> Eq (evalAt P c0 c1 (box B) pos) false
    allFalse e =
      fromGF (globalFulfil P b c0 c1 mbc cyc vp B (boxArgs_of (sub P) mA) e)
      where
        fromGF : Sigma Pos (\ q -> Prod (Mem q (orbitOf c0 c1 pos))
                                        (Eq (valOf P (posState q) B) false))
              -> Eq (evalAt P c0 c1 (box B) pos) false
        fromGF (sig q (prod mq eq)) =
          evalBox_false P c0 c1 B pos q mq
            (eqTrans (eqSym (ih q (orbitValid P b c0 c1 mc0 wc stb pos q vp mq)))
                     eq)

    onBox : (x : Bool) -> Eq (valOf P (posState pos) (box B)) x
         -> Eq (valOf P (posState pos) (box B)) (evalAt P c0 c1 (box B) pos)
    onBox true  e = eqTrans e (eqSym (allTrue e))
    onBox false e = eqTrans e (eqSym (allFalse e))

------------------------------------------------------------------------
-- Hintikka's lemma on a run, at every stage and at the start

hintRun : (P : Formula) (v0 : Val) (r : Run P v0) (A : Formula) -> Mem A (sub P)
       -> (i : Nat) -> Eq (valOf P (stateAt P v0 r i) A) (eval P v0 r A i)
hintRun P v0 (mkRun b c0 c1 mc0 wc stb mbc cyc rest mv0 wr) A mA i =
  hint P b c0 c1 mc0 wc stb mbc cyc A mA
       (posIter c0 c1 i (prod v0 rest))
       (posIterValid P b c0 c1 mc0 wc stb i (prod v0 rest) (vpos v0 rest mv0 wr))

hintStart : (P : Formula) (v0 : Val) (r : Run P v0) (A : Formula) -> Mem A (sub P)
         -> Eq (valOf P v0 A) (eval P v0 r A 0)
hintStart P v0 (mkRun b c0 c1 mc0 wc stb mbc cyc rest mv0 wr) A mA =
  hint P b c0 c1 mc0 wc stb mbc cyc A mA (prod v0 rest) (vpos v0 rest mv0 wr)

------------------------------------------------------------------------
-- What the two lemmas together say.
--
-- If a surviving state contains the formula the procedure was run on, that
-- formula is not refutable: Hintikka gives [[P]] = 1 at stage 0 of the lasso,
-- and soundness would give [[neg P]] = 1 there too.  This is the countermodel
-- half of Theorem 6.1, with only the packaging left for G28.

clash : (x : Bool) -> Eq x true -> Eq (boolNot x) true -> Empty
clash true  ex ()
clash false () en

notRefutable : (P : Formula) (v0 : Val) (r : Run P v0)
            -> Eq (valOf P v0 P) true -> Deriv (neg P) -> Empty
notRefutable P v0 (mkRun b c0 c1 mc0 wc stb mbc cyc rest mv0 wr) e d =
  clash (evalAt P c0 c1 P (prod v0 rest)) holds negated
  where
    r : Run P v0
    r = mkRun b c0 c1 mc0 wc stb mbc cyc rest mv0 wr

    holds : Eq (evalAt P c0 c1 P (prod v0 rest)) true
    holds = eqTrans (eqSym (hintStart P v0 r P (sub_self P))) e

    negated : Eq (boolNot (evalAt P c0 c1 P (prod v0 rest))) true
    negated = soundRun P v0 r d 0

-- and in the form the decision procedure produces it: if the procedure reports
-- P satisfiable -- some surviving state contains P -- then neg P is not
-- derivable in L.  No enumeration of derivations is involved; the lasso through
-- that state is the certificate.

notRefutableSat : (P : Formula) -> Eq (satB P) true -> Deriv (neg P) -> Empty
notRefutableSat P e d = go (anyL_true (\ v -> valOf P v P) (Uinf P) e)
  where
    go : Sigma Val (\ v -> Prod (Mem v (Uinf P)) (Eq (valOf P v P) true)) -> Empty
    go (sig v (prod m ev)) = notRefutable P v (runOf P v m (lasso P v m)) ev d

------------------------------------------------------------------------
-- Checkpoint.
--
-- dia p is consistent: neg (dia p) has no derivation in L.  This is a THEOREM,
-- not a computation -- the certificate is the two-state lasso of LTL.Lasso, and
-- the proof is Hintikka's lemma at stage 0 against soundness.

diaP_consistent : Deriv (neg diaP) -> Empty
diaP_consistent = notRefutableSat diaP satB_diaP
