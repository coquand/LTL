{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Gfp -- the set W of Theorem 4.1, case (R2), and the only property of it
-- the proof uses: that it is CLOSED under ->-steps inside U_k.
--
-- m4.tex writes the invariant as B = beta_W with W = Reach_{U_k}(v).  The two
-- facts wanted are that every state of W leaves the j-th eventuality pending
-- (step (i)) and that W is closed under successors lying in U_k (step (ii)).
-- Taking W to be the reachable set makes closure a theorem about the fixed
-- point of an ACCUMULATING iteration: acc grows, and one has to know that
-- |U_k| rounds are enough, which is a pigeonhole argument over a duplicate-free
-- accumulator.
--
-- Take instead the largest ->-closed set of states at which A still holds:
--
--    W_0 := { w in U_k : A in w },     W_{i+1} := { w in W_i : succ_{U_k}(w) subset W_i }
--
-- and W := the first W_i that is already closed.  This is a REMOVING
-- iteration, so closure comes out with no counting at all.  The price is that
-- (R2) now reads "v lies in W" rather than "A holds throughout Reach_{U_k}(v)";
-- gfpSound and gfpComplete at the end of this file show the two are the same
-- condition, with Reach given by its proper definition, the inductive type Path
-- of ->-paths inside U_k.  That is closer to the note than the fuel-bounded
-- reach of LTL.Reach, which only approximates Path from below.
--
-- G29 of FORMALISATION-PLAN.md.  Until Phase 8 the iteration was run for
-- length W_0 rounds and the fixed point was recovered afterwards, by
-- shrinkFix and filterL_allTrue, from a Le measure.  It is now run until the
-- round finds nothing to remove and STOPS THERE, with termination by recursion
-- on a Bar.  Three things come out of that.  The search does one pass instead
-- of |W_0| once it has converged, which is where most of checkpoint C5 was
-- going; the fixed-point equation disappears, since the closed case returns W
-- itself rather than an iterate of it; and the Le measure survives only inside
-- barOfList, where it is paid once.

module LTL.Gfp where

open import LTL.Closure public

------------------------------------------------------------------------
-- The greatest closed set of states at which A still holds.
--
-- holdsAt P A w says that the eventuality  box A  is NOT fulfilled at w, in the
-- terminology of m4.tex section 3: fulfilment is  A not in w .

holdsAt : Formula -> Formula -> Val -> Bool
holdsAt P A w = valOf P w A

wZero : Formula -> List Val -> Formula -> List Val
wZero P us A = filterL (holdsAt P A) us

succIn : Formula -> List Val -> List Val -> Val -> Bool
succIn P us W w = allB (\ w' -> boolImp (step P w w') (memB w' W)) us

shrink : Formula -> List Val -> List Val -> List Val
shrink P us W = filterL (succIn P us W) W

------------------------------------------------------------------------
-- The iteration, run until it stops.
--
-- findFalse asks the one question the round needs: is there a state of W with
-- a successor in us that has already left W?  If there is not, W is closed and
-- is the answer.  If there is, that state leaves W -- and it leaves the Bar's
-- predicate with it, which is what dropInE says and what makes the recursive
-- call structurally smaller.

shrinkGo   : (P : Formula) (us : List Val) {E : Val -> Bool} (W : List Val)
          -> InE E W -> IFin E -> List Val
shrinkFind : (P : Formula) (us : List Val) {E : Val -> Bool} (W : List Val)
          -> InE E W -> IFin E -> FindResult (succIn P us W) W -> List Val

shrinkGo P us W sb bar = shrinkFind P us W sb bar (findFalse (succIn P us W) W)

shrinkFind P us W sb bar      (allT f)      = W
shrinkFind P us W sb (cBar h) (found x m q) =
  shrinkGo P us (shrink P us W) (dropInE (succIn P us W) W sb x q) (h x (sb x m))

gfpW : Formula -> List Val -> Formula -> List Val
gfpW P us A = shrinkGo P us (wZero P us A) (memInE (wZero P us A))
                       (listBar (wZero P us A))

------------------------------------------------------------------------
-- Closure, which is what step (ii) of Theorem 4.1 needs

ClosedIn : Formula -> List Val -> List Val -> Set
ClosedIn P us W =
  (w w' : Val) -> Mem w W -> Mem w' us -> Eq (step P w w') true -> Mem w' W

closedOfAll : (P : Formula) (us W : List Val)
           -> ({x : Val} -> Mem x W -> Eq (succIn P us W x) true)
           -> ClosedIn P us W
closedOfAll P us W f w w' mw mw' st =
  memB_sound w' W
    (impTrueB (step P w w') (memB w' W)
              (allB_at (\ z -> boolImp (step P w z) (memB z W)) us mw' (f mw))
              st)

shrinkGoClosed   : (P : Formula) (us : List Val) {E : Val -> Bool} (W : List Val)
                -> (sb : InE E W) (bar : IFin E)
                -> ClosedIn P us (shrinkGo P us W sb bar)
shrinkFindClosed : (P : Formula) (us : List Val) {E : Val -> Bool} (W : List Val)
                -> (sb : InE E W) (bar : IFin E)
                -> (fr : FindResult (succIn P us W) W)
                -> ClosedIn P us (shrinkFind P us W sb bar fr)

shrinkGoClosed P us W sb bar =
  shrinkFindClosed P us W sb bar (findFalse (succIn P us W) W)

shrinkFindClosed P us W sb bar      (allT f)      = closedOfAll P us W f
shrinkFindClosed P us W sb (cBar h) (found x m q) =
  shrinkGoClosed P us (shrink P us W) (dropInE (succIn P us W) W sb x q)
                 (h x (sb x m))

gfpClosed : (P : Formula) (us : List Val) (A : Formula)
         -> ClosedIn P us (gfpW P us A)
gfpClosed P us A =
  shrinkGoClosed P us (wZero P us A) (memInE (wZero P us A))
                 (listBar (wZero P us A))

------------------------------------------------------------------------
-- The other two properties: W sits inside U_k, and A holds throughout it

shrinkGoSub   : (P : Formula) (us : List Val) {E : Val -> Bool} (W : List Val)
             -> (sb : InE E W) (bar : IFin E) {z : Val}
             -> Mem z (shrinkGo P us W sb bar) -> Mem z W
shrinkFindSub : (P : Formula) (us : List Val) {E : Val -> Bool} (W : List Val)
             -> (sb : InE E W) (bar : IFin E)
             -> (fr : FindResult (succIn P us W) W) {z : Val}
             -> Mem z (shrinkFind P us W sb bar fr) -> Mem z W

shrinkGoSub P us W sb bar =
  shrinkFindSub P us W sb bar (findFalse (succIn P us W) W)

shrinkFindSub P us W sb bar      (allT f)      mz = mz
shrinkFindSub P us W sb (cBar h) (found x m q) mz =
  filter_sub (succIn P us W) W
             (shrinkGoSub P us (shrink P us W)
                          (dropInE (succIn P us W) W sb x q) (h x (sb x m)) mz)

gfpWZero : (P : Formula) (us : List Val) (A : Formula) {w : Val}
        -> Mem w (gfpW P us A) -> Mem w (wZero P us A)
gfpWZero P us A =
  shrinkGoSub P us (wZero P us A) (memInE (wZero P us A))
              (listBar (wZero P us A))

gfpIn : (P : Formula) (us : List Val) (A : Formula) {w : Val}
     -> Mem w (gfpW P us A) -> Mem w us
gfpIn P us A m = filter_sub (holdsAt P A) us (gfpWZero P us A m)

gfpHolds : (P : Formula) (us : List Val) (A : Formula) {w : Val}
        -> Mem w (gfpW P us A) -> Eq (valOf P w A) true
gfpHolds P us A m = filter_prop (holdsAt P A) us (gfpWZero P us A m)

------------------------------------------------------------------------
-- Greatest: any closed family of states at which A holds is inside gfpW.
--
-- Stated for a family X : Val -> Set rather than a list, which is what lets
-- gfpComplete below instantiate it at Path.

shrinkGoGreatest   : (P : Formula) (us : List Val) {E : Val -> Bool} (W : List Val)
                  -> (sb : InE E W) (bar : IFin E) (X : Val -> Set)
                  -> ((w : Val) -> X w -> Mem w W)
                  -> ((w w' : Val) -> X w -> Mem w' us -> Eq (step P w w') true -> X w')
                  -> (w : Val) -> X w -> Mem w (shrinkGo P us W sb bar)
shrinkFindGreatest : (P : Formula) (us : List Val) {E : Val -> Bool} (W : List Val)
                  -> (sb : InE E W) (bar : IFin E)
                  -> (fr : FindResult (succIn P us W) W) (X : Val -> Set)
                  -> ((w : Val) -> X w -> Mem w W)
                  -> ((w w' : Val) -> X w -> Mem w' us -> Eq (step P w w') true -> X w')
                  -> (w : Val) -> X w -> Mem w (shrinkFind P us W sb bar fr)

shrinkGoGreatest P us W sb bar =
  shrinkFindGreatest P us W sb bar (findFalse (succIn P us W) W)

shrinkFindGreatest P us W sb bar      (allT f)      X inW cl w x = inW w x
shrinkFindGreatest P us W sb (cBar h) (found x0 m q) X inW cl w x =
  shrinkGoGreatest P us (shrink P us W) (dropInE (succIn P us W) W sb x0 q)
                   (h x0 (sb x0 m)) X inW' cl w x
  where
    inW' : (z : Val) -> X z -> Mem z (shrink P us W)
    inW' z xz =
      filter_true (succIn P us W) W (inW z xz)
                  (allB_intro (\ w' -> boolImp (step P z w') (memB w' W)) us inner)
      where
        inner : {w' : Val} -> Mem w' us
             -> Eq (boolImp (step P z w') (memB w' W)) true
        inner {w'} mw' =
          impIntroB (step P z w') (memB w' W)
                    (\ st -> memB_complete w' W (inW w' (cl z w' xz mw' st)))

gfpGreatest : (P : Formula) (us : List Val) (A : Formula) (X : Val -> Set)
           -> ((w : Val) -> X w -> Mem w us)
           -> ((w : Val) -> X w -> Eq (valOf P w A) true)
           -> ((w w' : Val) -> X w -> Mem w' us -> Eq (step P w w') true -> X w')
           -> (w : Val) -> X w -> Mem w (gfpW P us A)
gfpGreatest P us A X inUs hol cl =
  shrinkGoGreatest P us (wZero P us A) (memInE (wZero P us A))
                   (listBar (wZero P us A)) X
                   (\ w x -> filter_true (holdsAt P A) us (inUs w x) (hol w x)) cl

------------------------------------------------------------------------
-- Reach_U(v) of m4.tex section 3, as an inductive type of ->-paths inside U.

data Path (P : Formula) (us : List Val) : Val -> Val -> Set where
  pnil  : {v : Val} -> Path P us v v
  pcons : {v w x : Val} -> Mem w us -> Eq (step P v w) true
       -> Path P us w x -> Path P us v x

pathEnd : (P : Formula) (us : List Val) {v w : Val}
       -> Mem v us -> Path P us v w -> Mem w us
pathEnd P us mv pnil            = mv
pathEnd P us mv (pcons mw st p) = pathEnd P us mw p

pathSnoc : (P : Formula) (us : List Val) {v w w' : Val}
        -> Path P us v w -> Mem w' us -> Eq (step P w w') true -> Path P us v w'
pathSnoc P us pnil            mw' st' = pcons mw' st' pnil
pathSnoc P us (pcons mw st p) mw' st' = pcons mw st (pathSnoc P us p mw' st')

------------------------------------------------------------------------
-- (R2), the note's way and this one, are the same condition.

gfpPath : (P : Formula) (us : List Val) (A : Formula) {v w : Val}
       -> Mem v (gfpW P us A) -> Path P us v w -> Mem w (gfpW P us A)
gfpPath P us A m pnil            = m
gfpPath P us A m (pcons mw st p) =
  gfpPath P us A (gfpClosed P us A _ _ m mw st) p

-- v in gfpW  implies  the eventuality is fulfilled at no state reachable from v
gfpSound : (P : Formula) (us : List Val) (A : Formula) (v : Val)
        -> Mem v (gfpW P us A)
        -> (w : Val) -> Path P us v w -> Eq (valOf P w A) true
gfpSound P us A v m w p = gfpHolds P us A (gfpPath P us A m p)

-- and conversely
gfpComplete : (P : Formula) (us : List Val) (A : Formula) (v : Val)
           -> Mem v us
           -> ((w : Val) -> Path P us v w -> Eq (valOf P w A) true)
           -> Mem v (gfpW P us A)
gfpComplete P us A v mv h =
  gfpGreatest P us A (\ w -> Path P us v w)
              (\ w p -> pathEnd P us mv p)
              h
              (\ w w' p mw' st -> pathSnoc P us p mw' st)
              v pnil
