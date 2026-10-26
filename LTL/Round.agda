{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Round -- G22 of FORMALISATION-PLAN.md, the round of m4.tex section 5.
--
--   A round from u in U_inf is the finite path in U_inf obtained as follows.
--   Let u_0 := u.  For j = 1,...,m: if the j-th eventuality is pending at
--   u_{j-1}, let u_j be the endpoint of a path in U_inf from u_{j-1} to a state
--   fulfilling it, which exists by Lemma 5.1; otherwise u_j := u_{j-1} by the
--   empty path.  The round ends at u_m.
--
-- The construction is a recursion along the list of eventualities, and the
-- payload is the property Proposition 5.3 will use:
--
--   every eventuality pending at u is fulfilled at some state the round visits.
--
-- Note that this is pending at u = u_0, not at u_{j-1}, which is what the
-- construction tests.  walkPersist bridges the two, exactly as the note does:
-- along the walk built so far, a pending eventuality is either already
-- fulfilled -- and then there is nothing to do -- or still pending at the
-- endpoint, where the next stage of the recursion deals with it.
--
-- One extra step is appended at the end so that a round is never empty.  The
-- note does not need this because it reads the boundary sequence as a path;
-- here the cycle of Proposition 5.3 is assembled out of round walks, and a
-- cycle must contain at least one transition.

module LTL.Round where

open import LTL.Fix public

------------------------------------------------------------------------
-- The body of a round: the eventualities of As dealt with, in order

data RoundB (P : Formula) (As : List Formula) (u : Val) : Set where
  mkRoundB : (ws : List Val) (x : Val)
          -> Walk P (Uinf P) u ws x -> Mem x (Uinf P)
          -> ((A : Formula) -> Mem A As -> Eq (valOf P u (box A)) false
                -> Fulfil P A u ws)
          -> RoundB P As u

nilFul : (P : Formula) (u : Val) (A : Formula)
      -> Mem A ([] {A = Formula}) -> Eq (valOf P u (box A)) false -> Fulfil P A u []
nilFul P u A ()

roundBody : (P : Formula) (As : List Formula)
         -> ({A : Formula} -> Mem A As -> Mem A (boxArgs (sub P)))
         -> (u : Val) -> Mem u (Uinf P) -> RoundB P As u
roundBody P []        sbA u mu = mkRoundB [] u wnil mu (nilFul P u)
roundBody P (A :: As) sbA u mu = onPend (valOf P u (box A)) refl
  where
    -- ws1 takes u to x1, and deals with A if A was pending at u; the recursion
    -- then deals with As from x1.
    combine : (ws1 : List Val) (x1 : Val)
           -> Walk P (Uinf P) u ws1 x1 -> Mem x1 (Uinf P)
           -> (Eq (valOf P u (box A)) false -> Fulfil P A u ws1)
           -> RoundB P (A :: As) u
    combine ws1 x1 wk1 mx1 hA =
      go (roundBody P As (\ m -> sbA (memTl m)) x1 mx1)
      where
        go : RoundB P As x1 -> RoundB P (A :: As) u
        go (mkRoundB ws2 x2 wk2 mx2 h2) =
          mkRoundB (append ws1 ws2) x2 (walkApp P (Uinf P) wk1 wk2) mx2 prop
          where
            prop : (B : Formula) -> Mem B (A :: As)
                -> Eq (valOf P u (box B)) false -> Fulfil P B u (append ws1 ws2)
            prop B memHd     pd = fulApp ws1 ws2 (hA pd)
            prop B (memTl m) pd =
              sumElim (\ f   -> fulApp ws1 ws2 f)
                      (\ pd2 -> fulApp2 ws1 ws2 (walkEnd P (Uinf P) wk1) (h2 B m pd2))
                      (walkPersist P (Uinf P) B (boxArgs_mem (sub P) (sbA (memTl m)))
                                   wk1 pd)

    onPend : (b : Bool) -> Eq (valOf P u (box A)) b -> RoundB P (A :: As) u
    -- not pending at u: the empty path, and the obligation is vacuous
    onPend true  ep =
      combine [] u wnil mu
              (\ pd -> emptyElim (tfAbs (eqTrans (eqSym ep) pd)))
    -- pending at u: Lemma 5.1 supplies a walk to a state fulfilling it
    onPend false ep = fromEsc (uinfFulfil P u mu A (sbA memHd) ep)
      where
        fromEsc : Escape P (Uinf P) A u -> RoundB P (A :: As) u
        fromEsc (esc ws1 x1 wk1 mx1 ex) =
          combine ws1 x1 wk1 mx1 (\ pd -> ful x1 (walkEnd P (Uinf P) wk1) ex)

------------------------------------------------------------------------
-- A round, with the extra step that makes it nonempty

data Round (P : Formula) (u : Val) : Set where
  mkRound : (rs : List Val) (x : Val)
         -> Walk P (Uinf P) u rs x -> Mem x (Uinf P)
         -> Eq (nullB rs) false
         -> ((A : Formula) -> Mem A (boxArgs (sub P))
               -> Eq (valOf P u (box A)) false -> Fulfil P A u rs)
         -> Round P u

roundOf : (P : Formula) (u : Val) -> Mem u (Uinf P) -> Round P u
roundOf P u mu = fromBody (roundBody P (boxArgs (sub P)) (\ m -> m) u mu)
  where
    fromBody : RoundB P (boxArgs (sub P)) u -> Round P u
    fromBody (mkRoundB ws x wk mx h) = fromSucc (uinfSucc P x mx)
      where
        fromSucc : Succ P x -> Round P u
        fromSucc (succ y my st) =
          mkRound (append ws (y :: [])) y
                  (walkApp P (Uinf P) wk (wcons my st wnil)) my
                  (nullB_appR ws y [])
                  (\ A mA pd -> fulApp ws (y :: []) (h A mA pd))

------------------------------------------------------------------------
-- The list the note calls the round

roundList : (P : Formula) (u : Val) -> Round P u -> List Val
roundList P u (mkRound rs x wk mx nn h) = rs

round : (P : Formula) (u : Val) -> Mem u (Uinf P) -> List Val
round P u mu = roundList P u (roundOf P u mu)
