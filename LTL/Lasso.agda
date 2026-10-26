{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Lasso -- G23 of FORMALISATION-PLAN.md, Proposition 5.3 of m4.tex.
--
--   If U_inf is nonempty then from every v_0 in U_inf there is a fulfilling
--   lasso: a finite path v_0 -> ... -> v_p followed by a cycle
--   v_p -> ... -> v_q = v_p such that every eventuality pending at a state of
--   the cycle is fulfilled at a state of the cycle.
--
-- The note concatenates rounds, giving boundaries b_0 = v_0, b_1, b_2, ...,
-- and says that two of b_0,...,b_{|U_inf|} coincide "by the pigeonhole
-- principle for an explicitly given finite list, so the indices are found by
-- inspection".  That last clause is taken literally here: rather than proving
-- a pigeonhole lemma and then applying it, the search below carries the states
-- not yet used as a boundary and gives one up at each step.  A new boundary is
-- either one already seen -- and the cycle closes -- or a fresh one, which is
-- then given up.
--
-- Until Phase 8 those states were an explicit pool, with |U_inf| as fuel and a
-- Le measure saying the pool shortens; at fuel zero the pool was empty, so the
-- fresh case could not arise.  G29 replaces all of that by a Bar: the states
-- still available ARE the Bar's predicate E, giving one up is exactly the sub-
-- Bar  cBar  hands over, and the search terminates because Bar is well founded.
-- So the pool, the fuel, the measure and the base case all disappear together,
-- and what is left is the invariant  z in U_inf and z not yet a boundary
-- implies E z  -- which is the pigeonhole, still not a lemma.
--
-- The bookkeeping the note leaves implicit -- which prefix is the stem, which
-- suffix is the cycle -- is kept by recording, for each boundary b already
-- passed, a walk v_0 -> b AND a walk b -> current.  Both are extended as the
-- search advances, so when the current boundary turns out to equal b the two
-- halves are already in hand and nothing has to be split.
--
-- The cycle-fulfilment property is the note's argument verbatim: an eventuality
-- pending at a state s of the cycle is, by walkPersist along the cycle from s,
-- either fulfilled before the cycle closes or still pending at b -- and b's own
-- round is a prefix of the cycle, so it is fulfilled there.

module LTL.Lasso where

open import LTL.Round public

------------------------------------------------------------------------
-- A boundary already passed, with both halves of the eventual lasso

data Seen (P : Formula) (v0 cur b : Val) : Set where
  mkSeen : Mem b (Uinf P)
        -> (ps : List Val) -> Walk P (Uinf P) v0 ps b
        -> (qs : List Val) -> Walk P (Uinf P) b qs cur
        -> Eq (nullB qs) false
        -> ((A : Formula) -> Mem A (boxArgs (sub P))
              -> Eq (valOf P b (box A)) false -> Fulfil P A b qs)
        -> Seen P v0 cur b

seenExt : (P : Formula) (v0 cur nx b : Val) (rs : List Val)
       -> Walk P (Uinf P) cur rs nx -> Seen P v0 cur b -> Seen P v0 nx b
seenExt P v0 cur nx b rs wr (mkSeen mb ps wp qs wq nn h) =
  mkSeen mb ps wp (append qs rs) (walkApp P (Uinf P) wq wr)
         (nullB_appL qs rs nn)
         (\ A mA pd -> fulApp qs rs (h A mA pd))

------------------------------------------------------------------------
-- The lasso

data Lasso (P : Formula) (v0 : Val) : Set where
  mkLasso : (b : Val) -> Mem b (Uinf P)
         -> (ps : List Val) -> Walk P (Uinf P) v0 ps b
         -> (qs : List Val) -> Walk P (Uinf P) b qs b
         -> Eq (nullB qs) false
         -> ((s : Val) -> Mem s (b :: qs)
               -> (A : Formula) -> Mem A (boxArgs (sub P))
               -> Eq (valOf P s (box A)) false -> Fulfil P A b qs)
         -> Lasso P v0

-- Closing the loop.  This is where the cycle-fulfilment property is proved.

closeLasso : (P : Formula) (v0 cur : Val) -> Seen P v0 cur cur -> Lasso P v0
closeLasso P v0 cur (mkSeen mb ps wp qs wq nn h) =
  mkLasso cur mb ps wp qs wq nn cyc
  where
    cyc : (s : Val) -> Mem s (cur :: qs)
       -> (A : Formula) -> Mem A (boxArgs (sub P))
       -> Eq (valOf P s (box A)) false -> Fulfil P A cur qs
    cyc s ms A mA pd = fromSub (walkFrom P (Uinf P) wq ms)
      where
        fromSub : SubWalk P (Uinf P) s cur cur qs -> Fulfil P A cur qs
        fromSub (subWalk zs wz f) =
          sumElim mapFul (\ pd2 -> h A mA pd2)
                  (walkPersist P (Uinf P) A (boxArgs_mem (sub P) mA) wz pd)
          where
            mapFul : Fulfil P A s zs -> Fulfil P A cur qs
            mapFul (ful z m q) = ful z (f m) q

------------------------------------------------------------------------
-- The search.
--
-- Invariants: cur is reachable from v0 by the walk ps; bs lists the boundaries
-- already passed, each with its Seen record relative to the current position;
-- and every state of U_inf that is not yet a boundary still satisfies E, the
-- Bar's predicate.  That last one is Avail below, and it is the pigeonhole.

Avail : (Val -> Bool) -> Formula -> List Val -> Set
Avail E P bs = (z : Val) -> Mem z (Uinf P) -> Eq (memB z bs) false -> Eq (E z) true

-- Giving cur up: a state of U_inf outside cur :: bs is outside bs, hence
-- satisfies E, and is distinct from cur, hence survives the intersection with
-- neqB cur.

availCons : (P : Formula) {E : Val -> Bool} (bs : List Val) -> Avail E P bs
         -> (cur : Val) -> Avail (\ y -> boolAnd (E y) (neqB cur y)) P (cur :: bs)
availCons P {E} bs av cur z mz e =
  andIntro (E z) (neqB cur z)
           (av z mz (orFalseR (valEq z cur) (anyL (valEq z) bs) e))
           (eqCong boolNot (onEq (valEq cur z) refl))
  where
    onEq : (c : Bool) -> Eq (valEq cur z) c -> Eq (valEq cur z) false
    onEq false ec = ec
    onEq true  ec =
      emptyElim (tfAbs (eqTrans (eqSym (eqSubst (\ u -> Eq (valEq u cur) true)
                                                (valEq_sound cur z ec)
                                                (valEq_refl cur)))
                                (orFalseL (valEq z cur) (anyL (valEq z) bs) e)))

lassoSearch : (P : Formula) (v0 : Val) {E : Val -> Bool} -> IFin E
           -> (cur : Val) -> Mem cur (Uinf P)
           -> (ps : List Val) -> Walk P (Uinf P) v0 ps cur
           -> (bs : List Val)
           -> ((b : Val) -> Mem b bs -> Seen P v0 cur b)
           -> Avail E P bs
           -> Lasso P v0
lassoOn : (P : Formula) (v0 : Val) {E : Val -> Bool} -> IFin E
       -> (cur : Val) -> Mem cur (Uinf P)
       -> (ps : List Val) -> Walk P (Uinf P) v0 ps cur
       -> (bs : List Val)
       -> ((b : Val) -> Mem b bs -> Seen P v0 cur b)
       -> Avail E P bs
       -> (c : Bool) -> Eq (memB cur bs) c
       -> Lasso P v0

lassoSearch P v0 bar cur mcur ps wps bs seenf av =
  lassoOn P v0 bar cur mcur ps wps bs seenf av (memB cur bs) refl

lassoOn P v0 bar cur mcur ps wps bs seenf av true  ec =
  closeLasso P v0 cur (seenf cur (memB_sound cur bs ec))
lassoOn P v0 (cBar h) cur mcur ps wps bs seenf av false ec =
  fromRound (roundOf P cur mcur)
  where
    fromRound : Round P cur -> Lasso P v0
    fromRound (mkRound rs nx wr mnx nn hf) =
      lassoSearch P v0 (h cur (av cur mcur ec))
                  nx mnx (append ps rs) (walkApp P (Uinf P) wps wr)
                  (cur :: bs) seenf' (availCons P bs av cur)
      where
        seenf' : (b : Val) -> Mem b (cur :: bs) -> Seen P v0 nx b
        seenf' b memHd     = mkSeen mcur ps wps rs wr nn hf
        seenf' b (memTl m) = seenExt P v0 cur nx b rs wr (seenf b m)

------------------------------------------------------------------------
-- Proposition 5.3

lasso : (P : Formula) (v0 : Val) -> Mem v0 (Uinf P) -> Lasso P v0
lasso P v0 m =
  lassoSearch P v0 (listBar (Uinf P)) v0 m [] wnil [] noSeen
              (\ z mz e -> memB_complete z (Uinf P) mz)
  where
    noSeen : (b : Val) -> Mem b ([] {A = Val}) -> Seen P v0 v0 b
    noSeen b ()

------------------------------------------------------------------------
-- Projections, so that a lasso can be looked at

lassoStem : (P : Formula) (v0 : Val) -> Lasso P v0 -> List Val
lassoStem P v0 (mkLasso b mb ps wp qs wq nn cyc) = ps

lassoCycle : (P : Formula) (v0 : Val) -> Lasso P v0 -> List Val
lassoCycle P v0 (mkLasso b mb ps wp qs wq nn cyc) = qs

-- The lasso from a NAMED surviving state.  Taking whichever state U_inf happens
-- to list first is no use as an illustration once the state set is generated
-- from atom assignments and closed up from a seed (G30): the order is not the
-- order of allVecs, and the interesting state need not be the first one.

lassoAt : (P : Formula) (v : Val) -> Eq (memB v (Uinf P)) true
       -> Prod (List Val) (List Val)
lassoAt P v e = prod (lassoStem P v (lasso P v m)) (lassoCycle P v (lasso P v m))
  where
    m : Mem v (Uinf P)
    m = memB_sound v (Uinf P) e

------------------------------------------------------------------------
-- The lasso, computed.
--
-- For dia p the four positions of sub (dia p) are
--
--    neg (box (neg p)) ,  box (neg p) ,  neg p ,  p
--
-- and Uinf has the three states of Example 1 of lecture15.pdf, the first of
-- which is  1 0 1 0 : dia p holds, p does not.  Starting there, the stem is
-- empty -- the first boundary revisited is the start itself -- and the cycle is
--
--    1 0 1 0  ->  1 0 0 1  ->  1 0 1 0
--
-- of length two.  Its second state has p, so the eventuality that dia p leaves
-- pending is fulfilled on the cycle, which is what Proposition 5.3 promises and
-- what the type of cyc above records.  This is the countermodel to dia p: p
-- fails now and holds next, forever alternating.

sA : Val
sA = true :: false :: true :: false :: []
sB : Val
sB = true :: false :: false :: true :: []
sC : Val
sC = false :: true :: true :: false :: []

diaP_lasso : Eq (lassoAt diaP sA refl) (prod (sB :: sC :: []) (sC :: []))
diaP_lasso = refl


-- A degenerate but instructive second case.  For  box p  the demand-driven
-- state set has a single member: box p forces p by (S2) and carries itself
-- along every step by (T2), so the closure of the states containing box p is
-- the one state  1 1  looping to itself.  Nothing is pending there, every round
-- is the one forced step, and the cycle has length one.  That the cycle is
-- nonempty is not automatic; it is what the extra step appended by roundOf
-- buys, and Eq (nullB qs) false in mkLasso records it.

boxP : Formula
boxP = box (var zero)

sBox : Val
sBox = true :: true :: []

boxP_lasso : Eq (lassoAt boxP sBox refl) (prod [] (sBox :: []))
boxP_lasso = refl
