{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.SccLasso -- G38 of PHASE11-PLAN.md: an accepting component gives a lasso.
--
-- LTL.Graph proves the finite fair-graph certificate theorem with no formula in
-- it.  This file is one half of the translation layer: it reads the POSITIVE
-- answer of that theorem -- a FairLoop, i.e. a stem, a non-empty cycle and a
-- witness on the cycle for every fairness predicate -- as a Lasso of
-- Proposition 5.3, and hence as a Run.  The negative answer is G39 and is not
-- touched here.
--
-- There is little to it, and that is the point of G37 having been done first.
--
-- 1. Trail becomes Walk.  LTL.Graph's Trail is LTL.Walk's Walk with  step P
--    replaced by the abstract edge test G; at  G = step P  the two are the same
--    three fields, so trailWalk and walkTrail are two-clause inductions and not
--    constructions.  Nothing else is needed of the graph layer's paths.
--
-- 2. The fairness predicates are fixed.  For the eventuality  box A ,
--
--        evPred P A z  =  valOf P z (box A)  or  not (valOf P z A)
--
--    "box A is not pending at z, or A already fails at z", and evPreds P is one
--    of these for each A in  boxArgs (sub P) .  A cycle meeting evPred P A
--    either visits a state where the eventuality is not pending -- and then
--    persistence walks that back and it is pending nowhere on the cycle -- or
--    visits a state where A fails, which is fulfilment.  So RELEVANCE, which
--    the informal argument has to define ("the fairness sets relevant in C",
--    well defined only because a pending eventuality is uniform on a component)
--    is absorbed into the disjunction and the graph layer never hears of it.
--    That is why LTL.Graph knows only "C meets every f in fs".
--
-- 3. The cycle-fulfilment field of mkLasso is matched to those witnesses.  This
--    is the only real proof in the file and it is closeLasso's argument run
--    TWICE rather than once.  Given  box A  pending at a state s of the cycle:
--
--      walkPersist from s round to the base point r  --  either A is fulfilled
--        on the way, and we are done, or box A is still pending at r;
--      persistTo from r out to the witness z  --  either A is fulfilled on the
--        way, and we are done, or box A is still pending at z, and then
--        evPred's first disjunct is false at z, so its second is true, so A
--        fails at z, which is fulfilment at a state the cycle visits.
--
--    LTL.Walk has walkPersist, which reaches the ENDPOINT of a walk; the second
--    step needs it at a state VISITED, because the witness the graph layer
--    chooses is somewhere on the cycle and not at its base point.  persistTo
--    below is walkPersist with the target state carried along, and it is the
--    only new induction in the file.
--
-- The design decision, and it is the only one.
--
-- mkLasso's side conditions are all against  Uinf P :  Mem b (Uinf P) , and
-- both walks are  Walk P (Uinf P) .  LTL.Graph's vertices are whatever list it
-- is handed.  So the graph search has to be run somewhere inside Uinf P, and
-- sccLasso is stated for an arbitrary vertex list vs together with
--
--     (z : Val) -> Mem z vs -> Mem z (Uinf P)
--
-- so that "somewhere inside" is a parameter rather than a commitment.  The
-- instance taken here is  vs = Uinf P  with the identity inclusion.
--
-- At that instance the certificate branch is DEAD, and the second half of the
-- file proves it rather than asserting it: lassoFair turns the lasso
-- Proposition 5.3 already supplies into a FairLoop -- the converse translation,
-- and the place where the polarity of evPred is checked in the other direction
-- -- and then fairNoLoop, LTL.Graph's exclusivity theorem, refutes the
-- certificate.  So sccLassoOf has exactly the type of  lasso ,
--
--     (P : Formula) (v0 : Val) -> Mem v0 (Uinf P) -> Lasso P v0
--
-- and G38 is a second proof of Proposition 5.3 rather than a conditional one.
-- Note that this costs nothing to run: fairGraph returns inl, so the branch
-- calling  lasso  is never evaluated, and sccAt below is computed by the SCC
-- search alone.
--
-- Running the search instead at  Ust P , which is what G39's extraction will
-- want (Refuted quantifies over Ust P), would make the certificate branch live
-- and the LASSO branch the one needing work: a fair cycle in Ust P has a
-- successor at every state and fulfils every pending eventuality along itself,
-- so it survives every elimination round and lies in Uinf P -- but that
-- inclusion is a greatest-fixed-point induction over elimGo and is not G38.
-- Stating sccLasso with the inclusion as a hypothesis is exactly what leaves
-- that door open: G40 can supply it, or can keep the elimination and use the
-- identity.
--
-- Nothing in LTL.Extract, LTL.Elim or LTL.Lasso is touched, and the existing
-- positive tail -- runOf, Hintikka, buildCM -- consumes the result unchanged.

module LTL.SccLasso where

open import LTL.Run   public
open import LTL.Graph public

------------------------------------------------------------------------
-- Trails are walks, and walks are trails.
--
-- Trail us (step P) v zs w  is  Walk P us v zs w : same three fields, and
-- Eq (step P v x) true is Trail's edge field at  G = step P  on the nose.  The
-- graph layer's abstraction costs one induction to undo, in either direction.

trailWalk : (P : Formula) (us : List Val) {v : Val} {zs : List Val} {w : Val}
         -> Trail us (step P) v zs w -> Walk P us v zs w
trailWalk P us tNil          = wnil
trailWalk P us (tCons m e t) = wcons m e (trailWalk P us t)

walkTrail : (P : Formula) (us : List Val) {v : Val} {zs : List Val} {w : Val}
         -> Walk P us v zs w -> Trail us (step P) v zs w
walkTrail P us wnil            = tNil
walkTrail P us (wcons m e wk)  = tCons m e (walkTrail P us wk)

-- The base point of a non-empty cycle is a state the cycle visits.  Used in
-- both directions: to place the base point among mkLasso's states, and to see
-- that it lies in the vertex list.

walkLast : (P : Formula) (us : List Val) {v : Val} {zs : List Val} {w : Val}
        -> Walk P us v zs w -> Eq (nullB zs) false -> Mem w zs
walkLast P us wk nn = trailLast us (step P) (walkTrail P us wk) nn

------------------------------------------------------------------------
-- The fairness predicates.
--
-- One per eventuality of  boxArgs (sub P) .  Its FALSITY at z is exactly the
-- pair of hypotheses the refutation branch consumes -- box A pending at z, and
-- A holding at z -- which is why the same list of predicates will serve G39;
-- here only its truth at a witness is used, which is the disjunction read the
-- other way.

evPred : Formula -> Formula -> Val -> Bool
evPred P A z = boolOr (valOf P z (box A)) (boolNot (valOf P z A))

evPreds : Formula -> List (Val -> Bool)
evPreds P = map (evPred P) (boxArgs (sub P))

evPredsMem : (P : Formula) {A : Formula} -> Mem A (boxArgs (sub P))
          -> Mem (evPred P A) (evPreds P)
evPredsMem P m = memMap (evPred P) m

evPredsInv : (P : Formula) {g : Val -> Bool} -> Mem g (evPreds P)
          -> Sigma Formula
                   (\ A -> Prod (Mem A (boxArgs (sub P))) (Eq g (evPred P A)))
evPredsInv P m = map_mem_inv (evPred P) (boxArgs (sub P)) m

-- Reading a witness: the predicate holds at z and the eventuality is still
-- pending there, so the first disjunct is out and the second says A fails.

evWitness : (P : Formula) (A : Formula) (z : Val)
         -> Eq (evPred P A z) true -> Eq (valOf P z (box A)) false
         -> Eq (valOf P z A) false
evWitness P A z ez pd =
  sumElim (\ e1 -> emptyElim (tfAbs (eqTrans (eqSym e1) pd)))
          (\ e2 -> notTrue (valOf P z A) e2)
          (orTrue (valOf P z (box A)) (boolNot (valOf P z A)) ez)

-- and building one, from either disjunct.

evNotPending : (P : Formula) (A : Formula) (z : Val)
            -> Eq (valOf P z (box A)) true -> Eq (evPred P A z) true
evNotPending P A z e = orL (valOf P z (box A)) (boolNot (valOf P z A)) e

evFails : (P : Formula) (A : Formula) (z : Val)
       -> Eq (valOf P z A) false -> Eq (evPred P A z) true
evFails P A z e =
  orR (valOf P z (box A)) (boolNot (valOf P z A)) (eqCong boolNot e)

------------------------------------------------------------------------
-- Persistence to a state VISITED, not to the endpoint.
--
-- walkPersist (LTL/Walk.agda:127) says: along a walk with box A pending at the
-- start, either A is fulfilled at a state visited or box A is still pending at
-- the END.  Here the second alternative is wanted at an arbitrary visited
-- state.  The induction is walkPersist's own -- the step is persist, i.e. (T3)
-- -- with the target carried along and the walk cut short when it is reached.

persistTo : (P : Formula) (us : List Val) (A : Formula) -> Mem (box A) (sub P)
         -> {v : Val} {ws : List Val} {x : Val} -> Walk P us v ws x
         -> Eq (valOf P v (box A)) false
         -> {z : Val} -> Mem z ws
         -> Sum (Fulfil P A v ws) (Eq (valOf P z (box A)) false)
persistTo P us A mb wnil e ()
persistTo P us A mb (wcons {v} {w} {ws} {x} mw st wk) e {z} mz =
  onA (valOf P v A) refl z mz
  where
    onA : (b : Bool) -> Eq (valOf P v A) b -> (y : Val) -> Mem y (w :: ws)
       -> Sum (Fulfil P A v (w :: ws)) (Eq (valOf P y (box A)) false)
    onA false ea y my        = inl (ful v memHd ea)
    onA true  ea y memHd     = inr (persist P v w A mb st e ea)
    onA true  ea y (memTl k) =
      sumElim (\ f -> inl (fulTl f)) inr
              (persistTo P us A mb wk (persist P v w A mb st e ea) k)

------------------------------------------------------------------------
-- G38.
--
-- A FairLoop of LTL.Graph, inside any vertex list contained in Uinf P, is a
-- Lasso of Proposition 5.3.

sccLasso : (P : Formula) (vs : List Val)
        -> ((z : Val) -> Mem z vs -> Mem z (Uinf P))
        -> (v0 : Val) -> FairLoop vs (step P) (evPreds P) v0 -> Lasso P v0
sccLasso P vs sb v0 (fairLoop r st cy ts tc nn wit) =
  mkLasso r mr st wst cy wcy nn cyc
  where
    -- The cycle is non-empty, so its base point is a state it visits, and every
    -- state it visits lies in the vertex list.
    mr : Mem r (Uinf P)
    mr = sb r (trailIn vs (step P) tc (trailLast vs (step P) tc nn))

    wst : Walk P (Uinf P) v0 st r
    wst = trailWalk P (Uinf P) (trailMono vs (Uinf P) (step P) sb ts)

    wcy : Walk P (Uinf P) r cy r
    wcy = trailWalk P (Uinf P) (trailMono vs (Uinf P) (step P) sb tc)

    cyc : (s : Val) -> Mem s (r :: cy)
       -> (A : Formula) -> Mem A (boxArgs (sub P))
       -> Eq (valOf P s (box A)) false -> Fulfil P A r cy
    cyc s ms A mA pd = fromSub (walkFrom P (Uinf P) wcy ms)
      where
        mbx : Mem (box A) (sub P)
        mbx = boxArgs_mem (sub P) mA

        -- Still pending at the base point: go out to the witness the graph
        -- layer chose for evPred P A.
        atR : Eq (valOf P r (box A)) false -> Fulfil P A r cy
        atR pr = onW (wit (evPred P A) (evPredsMem P mA))
          where
            onW : Sigma Val (\ z -> Prod (Mem z cy) (Eq (evPred P A z) true))
               -> Fulfil P A r cy
            onW (sig z (prod mz ez)) =
              sumElim (\ f -> f)
                      (\ pz -> ful z (memTl mz) (evWitness P A z ez pz))
                      (persistTo P (Uinf P) A mbx wcy pr mz)

        -- Travelling along the cycle from s, as Proposition 5.3 does.
        fromSub : SubWalk P (Uinf P) s r r cy -> Fulfil P A r cy
        fromSub (subWalk zs wz f) =
          sumElim mapFul atR (walkPersist P (Uinf P) A mbx wz pd)
          where
            mapFul : Fulfil P A s zs -> Fulfil P A r cy
            mapFul (ful z m q) = ful z (f m) q

-- and hence a Run: the existing positive tail, unchanged.

sccRun : (P : Formula) (vs : List Val)
      -> ((z : Val) -> Mem z vs -> Mem z (Uinf P))
      -> (v0 : Val) -> Mem v0 (Uinf P)
      -> FairLoop vs (step P) (evPreds P) v0 -> Run P v0
sccRun P vs sb v0 mv0 fl = runOf P v0 mv0 (sccLasso P vs sb v0 fl)

------------------------------------------------------------------------
-- The converse, which is what makes the instance at Uinf P total.
--
-- A fulfilling lasso IS a fair loop for evPreds P.  For each eventuality: if it
-- is not pending at the base point, the base point is its own witness -- and it
-- lies ON the cycle because the cycle is non-empty; if it is pending there, the
-- lasso's own cycle-fulfilment field supplies a state of the cycle where A
-- fails, which is the other disjunct.  This is the polarity of evPred checked
-- from the other side.

lassoFair : (P : Formula) (v0 : Val) -> Lasso P v0
         -> FairLoop (Uinf P) (step P) (evPreds P) v0
lassoFair P v0 (mkLasso b mb ps wp qs wq nn cyc) =
  fairLoop b ps qs (walkTrail P (Uinf P) wp) (walkTrail P (Uinf P) wq) nn each
  where
    mbq : Mem b qs
    mbq = walkLast P (Uinf P) wq nn

    forA : (A : Formula) -> Mem A (boxArgs (sub P))
        -> Sigma Val (\ z -> Prod (Mem z qs) (Eq (evPred P A z) true))
    forA A mA = onPend (valOf P b (box A)) refl
      where
        onPend : (c : Bool) -> Eq (valOf P b (box A)) c
              -> Sigma Val (\ z -> Prod (Mem z qs) (Eq (evPred P A z) true))
        onPend true  ep = sig b (prod mbq (evNotPending P A b ep))
        onPend false ep = onFul (cyc b memHd A mA ep)
          where
            onFul : Fulfil P A b qs
                 -> Sigma Val (\ z -> Prod (Mem z qs) (Eq (evPred P A z) true))
            onFul (ful z m q) = sig z (prod (onMem m) (evFails P A z q))
              where
                onMem : Mem z (b :: qs) -> Mem z qs
                onMem memHd     = mbq
                onMem (memTl k) = k

    each : (g : Val -> Bool) -> Mem g (evPreds P)
        -> Sigma Val (\ z -> Prod (Mem z qs) (Eq (g z) true))
    each g mg = onInv (evPredsInv P mg)
      where
        onInv : Sigma Formula
                      (\ A -> Prod (Mem A (boxArgs (sub P))) (Eq g (evPred P A)))
             -> Sigma Val (\ z -> Prod (Mem z qs) (Eq (g z) true))
        onInv (sig A (prod mA eg)) =
          eqSubst (\ h -> Sigma Val (\ z -> Prod (Mem z qs) (Eq (h z) true)))
                  (eqSym eg) (forA A mA)

------------------------------------------------------------------------
-- The instance: the search run on Uinf P itself, and it always finds the loop.

uinfFair : (P : Formula) (v0 : Val) -> Mem v0 (Uinf P)
        -> Sum (FairLoop (Uinf P) (step P) (evPreds P) v0)
               (Cert (step P) (evPreds P) (reachSet (Uinf P) (step P) v0))
uinfFair P v0 mv0 = fairGraph (Uinf P) (step P) (evPreds P) v0 mv0

-- Proposition 5.3, again.  The certificate branch is refuted by fairNoLoop
-- against the loop  lasso  already supplies; since fairGraph in fact returns
-- inl, that branch is never evaluated and  lasso  is never run.

sccLassoOf : (P : Formula) (v0 : Val) -> Mem v0 (Uinf P) -> Lasso P v0
sccLassoOf P v0 mv0 = sumElim yes no (uinfFair P v0 mv0)
  where
    yes : FairLoop (Uinf P) (step P) (evPreds P) v0 -> Lasso P v0
    yes fl = sccLasso P (Uinf P) (\ z m -> m) v0 fl

    no : Cert (step P) (evPreds P) (reachSet (Uinf P) (step P) v0) -> Lasso P v0
    no c = emptyElim (fairNoLoop (Uinf P) (step P) (evPreds P) v0 mv0 c
                                 (lassoFair P v0 (lasso P v0 mv0)))

sccRunOf : (P : Formula) (v0 : Val) -> Mem v0 (Uinf P) -> Run P v0
sccRunOf P v0 mv0 = runOf P v0 mv0 (sccLassoOf P v0 mv0)

------------------------------------------------------------------------
-- Projections, so that the two procedures can be set side by side.  lassoAt of
-- LTL.Lasso reads the round-based search the same way, so sccAt and lassoAt are
-- two Prod (List Val) (List Val) to be compared.

sccAt : (P : Formula) (v : Val) -> Eq (memB v (Uinf P)) true
     -> Prod (List Val) (List Val)
sccAt P v e = prod (lassoStem P v l) (lassoCycle P v l)
  where
    l : Lasso P v
    l = sccLassoOf P v (memB_sound v (Uinf P) e)

sccState : (P : Formula) (v0 : Val) -> Eq (memB v0 (Uinf P)) true -> Nat -> Val
sccState P v0 e i = stateAt P v0 (sccRunOf P v0 m) i
  where
    m : Mem v0 (Uinf P)
    m = memB_sound v0 (Uinf P) e

------------------------------------------------------------------------
-- The lassos, computed, beside the ones LTL.Lasso records.
--
-- For  dia p  the stem is the same and the cycle is the base point twice where
-- lassoSearch has it once.  That is not an accident of this example: mkCirc
-- always starts from the bare loop found by loopAt and prepends one LEG per
-- fairness predicate, each leg being the loop again followed by the trip out to
-- the witness and back.  Here there is one eventuality, its witness in the
-- terminal component {sC} is sC itself, so both halves of the trip are empty
-- and the leg is the bare loop over again.  The SCC construction chooses its
-- witnesses in its own order and does not produce the shortest fair cycle --
-- which is the observation checkpoint C8 is to make, not a defect.

sccDiaP : Eq (sccAt diaP sA refl) (prod (sB :: sC :: []) (sC :: sC :: []))
sccDiaP = refl

lassoDiaP : Eq (lassoAt diaP sA refl) (prod (sB :: sC :: []) (sC :: []))
lassoDiaP = refl

-- and the same doubling in the degenerate case, where the state set is one
-- state looping to itself.

sccBoxP : Eq (sccAt boxP sBox refl) (prod [] (sBox :: sBox :: []))
sccBoxP = refl

lassoBoxP : Eq (lassoAt boxP sBox refl) (prod [] (sBox :: []))
lassoBoxP = refl

-- The run, unwound, to show that runOf accepts the result unchanged: the stem
-- of dia p walked out, then the cycle forever.

sccDiaP_run : Eq (map (sccState diaP sA refl) (0 :: 1 :: 2 :: 3 :: 4 :: 5 :: []))
                 (sA :: sB :: sC :: sC :: sC :: sC :: [])
sccDiaP_run = refl
