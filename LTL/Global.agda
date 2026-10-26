{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Global -- G24 of FORMALISATION-PLAN.md, Lemma 5.4 of m4.tex.
--
--   For every i and every box A in Sub(phi) with box A not in v_i, there is
--   j >= i with A not in v_j.
--
-- The note's proof splits on whether v_i lies on the cycle or on the stem, and
-- runs persistence forward along the stem to reduce the second case to the
-- first.  Here there is no such split: walkPersist does both at once.  A valid
-- position (s , rest) carries a walk from s to b, the cycle's end, whatever
-- part of the run s sits on; applying persistence to that walk gives either a
-- fulfilling state among s :: rest -- which is the stem case, and also the
-- "fulfilled before the cycle closes" half of the cycle case -- or the
-- eventuality still pending at b, where the cycle-fulfilment property of
-- Proposition 5.3 finishes it.
--
-- The conclusion is stated as membership in the forward orbit, which is the
-- form G27 needs: [[box A]] is a conjunction over the orbit, so a false
-- conjunct is exactly what refutes it.  globalFulfilAfter recovers the note's
-- "j >= i" reading from it.

module LTL.Global where

open import LTL.Run public

------------------------------------------------------------------------
-- b is a state of the cycle, so the two readings of "on the cycle" agree

cycMem : {b z : Val} {c0 : Val} {c1 : List Val}
      -> Mem b (c0 :: c1) -> Mem z (b :: c0 :: c1) -> Mem z (c0 :: c1)
cycMem mb memHd     = mb
cycMem mb (memTl m) = m

------------------------------------------------------------------------
-- Lemma 5.4

globalFulfil : (P : Formula) (b c0 : Val) (c1 : List Val)
            -> Mem b (c0 :: c1)
            -> ((s : Val) -> Mem s (b :: c0 :: c1)
                  -> (A : Formula) -> Mem A (boxArgs (sub P))
                  -> Eq (valOf P s (box A)) false -> Fulfil P A b (c0 :: c1))
            -> {pos : Pos} -> ValidPos P b pos
            -> (A : Formula) -> Mem A (boxArgs (sub P))
            -> Eq (valOf P (posState pos) (box A)) false
            -> Sigma Pos (\ q -> Prod (Mem q (orbitOf c0 c1 pos))
                                      (Eq (valOf P (posState q) A) false))
globalFulfil P b c0 c1 mbc cyc (vpos s rest ms wk) A mA pend =
  sumElim onStem onCycle
          (walkPersist P (Uinf P) A (boxArgs_mem (sub P) mA) wk pend)
  where
    place : (q : Pos) -> Mem q (orbitOf c0 c1 (prod s rest)) -> {z : Val}
         -> Eq (posState q) z -> Eq (valOf P z A) false
         -> Sigma Pos (\ q' -> Prod (Mem q' (orbitOf c0 c1 (prod s rest)))
                                    (Eq (valOf P (posState q') A) false))
    place q mq eq ez =
      sig q (prod mq (eqSubst (\ y -> Eq (valOf P y A) false) (eqSym eq) ez))

    -- fulfilled before b is reached
    onStem : Fulfil P A s rest
          -> Sigma Pos (\ q -> Prod (Mem q (orbitOf c0 c1 (prod s rest)))
                                    (Eq (valOf P (posState q) A) false))
    onStem (ful z mz ez) = fromPL (posList_mem s rest mz)
      where
        fromPL : Sigma Pos (\ q -> Prod (Mem q (posList s rest)) (Eq (posState q) z))
              -> Sigma Pos (\ q -> Prod (Mem q (orbitOf c0 c1 (prod s rest)))
                                        (Eq (valOf P (posState q) A) false))
        fromPL (sig q (prod mq eq)) =
          place q (orbitStem c0 c1 s rest q mq) eq ez

    -- still pending at b: Proposition 5.3 fulfils it on the cycle
    onCycle : Eq (valOf P b (box A)) false
           -> Sigma Pos (\ q -> Prod (Mem q (orbitOf c0 c1 (prod s rest)))
                                     (Eq (valOf P (posState q) A) false))
    onCycle pb = fromFul (cyc b memHd A mA pb)
      where
        fromFul : Fulfil P A b (c0 :: c1)
               -> Sigma Pos (\ q -> Prod (Mem q (orbitOf c0 c1 (prod s rest)))
                                         (Eq (valOf P (posState q) A) false))
        fromFul (ful z mz ez) = fromPL (posList_mem c0 c1 (cycMem mbc mz))
          where
            fromPL : Sigma Pos (\ q -> Prod (Mem q (posList c0 c1))
                                            (Eq (posState q) z))
                  -> Sigma Pos (\ q -> Prod (Mem q (orbitOf c0 c1 (prod s rest)))
                                            (Eq (valOf P (posState q) A) false))
            fromPL (sig q (prod mq eq)) =
              place q (orbitCycle c0 c1 s rest q mq) eq ez

------------------------------------------------------------------------
-- The note's reading: some LATER state of the run fulfils it.
--
-- j = i + t, so j >= i is built into the statement rather than asserted.

globalFulfilAfter : (P : Formula) (b c0 : Val) (c1 : List Val)
                 -> Mem b (c0 :: c1)
                 -> ((s : Val) -> Mem s (b :: c0 :: c1)
                       -> (A : Formula) -> Mem A (boxArgs (sub P))
                       -> Eq (valOf P s (box A)) false -> Fulfil P A b (c0 :: c1))
                 -> (start : Pos) (i : Nat)
                 -> ValidPos P b (posIter c0 c1 i start)
                 -> (A : Formula) -> Mem A (boxArgs (sub P))
                 -> Eq (valOf P (posState (posIter c0 c1 i start)) (box A)) false
                 -> Sigma Nat (\ t ->
                      Eq (valOf P (posState (posIter c0 c1 (plus i t) start)) A) false)
globalFulfilAfter P b c0 c1 mbc cyc start i vp A mA pend =
  fromOrbit (globalFulfil P b c0 c1 mbc cyc vp A mA pend)
  where
    fromOrbit : Sigma Pos (\ q -> Prod (Mem q (orbitOf c0 c1 (posIter c0 c1 i start)))
                                       (Eq (valOf P (posState q) A) false))
             -> Sigma Nat (\ t ->
                  Eq (valOf P (posState (posIter c0 c1 (plus i t) start)) A) false)
    fromOrbit (sig q (prod mq eq)) =
      fromIter (orbitOf_iter c0 c1 (posIter c0 c1 i start) q mq)
      where
        fromIter : Sigma Nat (\ t -> Eq (posIter c0 c1 t (posIter c0 c1 i start)) q)
                -> Sigma Nat (\ t ->
                     Eq (valOf P (posState (posIter c0 c1 (plus i t) start)) A) false)
        fromIter (sig t et) =
          sig t (eqSubst (\ r -> Eq (valOf P (posState r) A) false)
                         (eqSym (eqTrans (posIter_plus c0 c1 i t start) et))
                         eq)
