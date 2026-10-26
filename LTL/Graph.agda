{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Graph -- G37 of PHASE11-PLAN.md: the finite fair-graph certificate
-- theorem, and nothing else.
--
--   Finite fair-graph certificate theorem.
--   Given a finite graph, finitely many decidable fairness predicates F_i, and
--   a vertex v, compute either
--     (a) a lasso from v whose cycle meets every relevant F_i, or
--     (b) a well-founded certificate that every recurrent component reachable
--         from v misses some F_i.
--
-- That is  fairGraph , at the bottom of the file.  (a) is FairLoop, (b) is Cert,
-- and certAll is the induction principle Cert exists to supply.
--
-- THERE IS NO LOGIC IN THIS MODULE.  No Formula occurs anywhere in it; the
-- graph is a list of vertices  vs : List Val  with an edge test
-- G : Val -> Val -> Bool , and the fairness sets are boolean predicates
-- fs : List (Val -> Bool) .  Val is used only because LTL.Bar's inductive
-- finiteness is stated for it; nothing here reads a bit of a valuation.
--
-- Where "relevant" went.  The informal statement quantifies over the fairness
-- sets RELEVANT in a component, which is well defined only because the pending
-- eventuality is uniform on a component (walkPersist).  Here relevance is
-- absorbed into the predicate: the caller passes, for the eventuality  box A ,
-- the predicate "box A is not pending, or A fails", so a component in which the
-- eventuality is not pending meets it for free and a component in which it is
-- pending meets it exactly by fulfilling it.  The graph layer therefore knows
-- only "C meets every f in fs", and the LTL reading of fs is G38 and G39.
--
-- The four things PHASE11-PLAN.md warns about, and what happened to each.
--
-- 1. Mutual reachability is reachability COMPLETELY, which is what LTL/Reach.agda
--    abandoned.  It is paid the way G30 paid: reachGo is a GROWING search whose
--    stopping condition is that a round adds nothing -- closeGo of LTL.Closure
--    with the seed changed from "contains P" to "is v" -- and completeness comes
--    from the stopping condition (reachSeed, reachClosed) rather than from a
--    bound.  There is no fuel and no claim that  length vs  rounds suffice.
--
-- 2. No component objects and no quotients.  A component is a representative
--    plus filterL:  sccOf vs G r = the w in reach(r) that reach r back.  The
--    condensation is never built; "r's component is terminal" is the boolean
--    termB, and a condensation edge is followed by moving the representative.
--
-- 3. No rank function and no topological sort.  graphGo is a REMOVING iteration
--    -- pick a sink or a terminal component, refute it, delete it -- so barRec
--    covers termination.  What needed proof is only that a non-empty graph has
--    a terminal component, and that is findTerm: follow condensation edges,
--    which is a third Bar search, terminating because the reachable set of the
--    new representative avoids every representative already visited.  The
--    invariant that says so is a single hypothesis, not a history list.
--
-- 4. The guardBar heap trap of section 4g.  Every Bar here comes from listBar,
--    i.e. from barOfList, which recurses on  length xs  and is blocked while
--    the list is a variable; guardBar is not used at all, so the 2^k unfolding
--    cannot happen.  TermRes and Block do mention reachSet and termB in their
--    constructor types -- and Agda normalises those -- but reachGo is blocked
--    at findFalse on a variable list, so nothing expands.  A growing search on
--    vectors would have needed the guard; a search over a list in hand does not.
--
-- The two answers are proved EXCLUSIVE, and that is the second half of the file.
-- certNoCirc: a Cert for ws forbids a fair circuit inside ws; fairNoLoop and
-- fairComplete carry it to the top, so the negative answer is a decision and not
-- merely an output.  This is the lecture's "key insight" done finitely.  The
-- lecture says an INFINITE path eventually stays inside one SCC, which needs
-- coinduction and a classical step; what is actually needed is the same thing
-- about a FINITE cycle, and that is two inductions on a trail --
--
--   a vertex on a cycle has a successor,  so a sink lies on no cycle;
--   any vertex of a cycle reaches any other,  so a cycle that enters a
--     successor-closed block never leaves it.
--
-- So no infinite path is constructed, nothing is coinductive, and no pigeonhole
-- is used, which are the same three absences section 4f claims for the rest of
-- the development.  Both sides are inhabited and neither theorem is vacuous:
-- cy_QS exhibits a Circuit and cert_P a Cert, at the bottom.
--
-- What this still does NOT do.  It decides nothing about formulas and builds no
-- derivation; the LTL reading of (b) is G39, where certAll's two hypotheses are
-- extractR1's and extractR2's on the nose -- Eq (nullB (outs ws G x)) true IS
-- Eq (r1 P ws x) true definitionally, and the block case supplies the closed set
-- and the unfulfilled eventuality that (Ind) needs.  Nor does it claim to be
-- cheaper than gfpW.
--
-- It is, in short, the factoring the current development has nowhere: Gfp, Elim,
-- Trace, Round and Lasso all mention formulas, and this file does not.

module LTL.Graph where

open import LTL.Bar public

------------------------------------------------------------------------
-- Glue

appNotNull : {A : Set} (xs ys : List A) -> Eq (nullB xs) false
          -> Eq (nullB (append xs ys)) false
appNotNull []        ys ()
appNotNull (x :: xs) ys e = refl

nullMemB : (ws : List Val) (z : Val) -> Eq (nullB ws) true -> Eq (memB z ws) false
nullMemB []        z e = refl
nullMemB (w :: ws) z ()

-- Reading  not (a and b) = true  when a is true.  okAccIn of LTL.Closure, which
-- is on the other side of Bar and cannot be imported here.

missTrue : (a b : Bool) -> Eq (boolNot (boolAnd a b)) true -> Eq a true -> Eq b false
missTrue true  true  () e
missTrue true  false q  e = refl
missTrue false b     q  ()

-- The out-neighbours of x inside ws.  For G = step P this is succs P ws x on
-- the nose, which is what G39 needs of it.

outs : List Val -> (Val -> Val -> Bool) -> Val -> List Val
outs ws G x = filterL (G x) ws

hasOut : List Val -> (Val -> Val -> Bool) -> Val -> Bool
hasOut ws G x = boolNot (nullB (outs ws G x))

------------------------------------------------------------------------
-- Trails: finite paths inside ws, carrying the list of vertices visited and
-- indexed by the endpoint.  LTL.Walk with  step P  replaced by G, and for the
-- same reason -- indexing by the endpoint keeps every concatenation free of
-- equational bookkeeping.  Reflexive-transitive; a cycle is a trail from r to r
-- whose list is non-empty, and that is the only place non-emptiness is needed.

data Trail (ws : List Val) (G : Val -> Val -> Bool) : Val -> List Val -> Val -> Set where
  tNil  : {v : Val} -> Trail ws G v [] v
  tCons : {v x : Val} {zs : List Val} {w : Val}
       -> Mem x ws -> Eq (G v x) true -> Trail ws G x zs w
       -> Trail ws G v (x :: zs) w

trailApp : (ws : List Val) (G : Val -> Val -> Bool) {u v w : Val} {xs zs : List Val}
        -> Trail ws G u xs v -> Trail ws G v zs w -> Trail ws G u (append xs zs) w
trailApp ws G tNil           t2 = t2
trailApp ws G (tCons m e t1) t2 = tCons m e (trailApp ws G t1 t2)

trailEnd : (ws : List Val) (G : Val -> Val -> Bool) {v : Val} {zs : List Val} {w : Val}
        -> Trail ws G v zs w -> Mem w (v :: zs)
trailEnd ws G tNil          = memHd
trailEnd ws G (tCons m e t) = memTl (trailEnd ws G t)

-- A trail that takes at least one step ends at a vertex it visits.

trailLast : (ws : List Val) (G : Val -> Val -> Bool) {v : Val} {zs : List Val} {w : Val}
         -> Trail ws G v zs w -> Eq (nullB zs) false -> Mem w zs
trailLast ws G tNil          ()
trailLast ws G (tCons m e t) nn = trailEnd ws G t

trailIn : (ws : List Val) (G : Val -> Val -> Bool) {v : Val} {zs : List Val} {w : Val}
       -> Trail ws G v zs w -> {z : Val} -> Mem z zs -> Mem z ws
trailIn ws G tNil          ()
trailIn ws G (tCons m e t) memHd     = m
trailIn ws G (tCons m e t) (memTl k) = trailIn ws G t k

trailMono : (ws vs : List Val) (G : Val -> Val -> Bool)
         -> ((z : Val) -> Mem z ws -> Mem z vs)
         -> {v : Val} {zs : List Val} {w : Val}
         -> Trail ws G v zs w -> Trail vs G v zs w
trailMono ws vs G sb tNil                  = tNil
trailMono ws vs G sb (tCons {x = x} m e t) =
  tCons (sb x m) e (trailMono ws vs G sb t)

data Reaches (ws : List Val) (G : Val -> Val -> Bool) (v w : Val) : Set where
  reachesBy : (zs : List Val) -> Trail ws G v zs w -> Reaches ws G v w

------------------------------------------------------------------------
-- The reachable set, as a growing search.
--
-- closeGo of LTL.Closure with two changes: the seed is "is v" instead of
-- "contains P", and the ambient candidate list is the vertex list rather than
-- StC P.  A round adds every vertex of ws that is wanted -- is v, or is a
-- G-successor of something already in acc -- and is not there yet; when a round
-- adds nothing, acc contains every wanted vertex, and THAT is completeness.
-- No round is counted.

rWant : (Val -> Val -> Bool) -> Val -> List Val -> Val -> Bool
rWant G v acc x = boolOr (valEq v x) (anyL (\ y -> G y x) acc)

rMiss : (Val -> Val -> Bool) -> Val -> List Val -> Val -> Bool
rMiss G v acc x = boolAnd (rWant G v acc x) (boolNot (memB x acc))

rOk : (Val -> Val -> Bool) -> Val -> List Val -> Val -> Bool
rOk G v acc x = boolNot (rMiss G v acc x)

rAdd : List Val -> (Val -> Val -> Bool) -> Val -> List Val -> List Val
rAdd ws G v acc = append (filterL (rMiss G v acc) ws) acc

rMissOf : (G : Val -> Val -> Bool) (v : Val) (acc : List Val) (x : Val)
       -> Eq (rOk G v acc x) false -> Eq (rMiss G v acc x) true
rMissOf G v acc x q = notFalse (rMiss G v acc x) q

rOutAcc : (G : Val -> Val -> Bool) (v : Val) (acc : List Val) (x : Val)
       -> Eq (rOk G v acc x) false -> Eq (memB x acc) false
rOutAcc G v acc x q =
  notTrue (memB x acc)
          (andTrueR (rWant G v acc x) (boolNot (memB x acc)) (rMissOf G v acc x q))

rInAdd : (ws : List Val) (G : Val -> Val -> Bool) (v : Val) (acc : List Val) (x : Val)
      -> Mem x ws -> Eq (rOk G v acc x) false -> Mem x (rAdd ws G v acc)
rInAdd ws G v acc x m q =
  memAppL (filterL (rMiss G v acc) ws) acc
          (filter_true (rMiss G v acc) ws m (rMissOf G v acc x q))

reachGo   : (ws : List Val) (G : Val -> Val -> Bool) (v : Val) {E : Val -> Bool}
            (acc : List Val)
         -> ((z : Val) -> Mem z ws -> Eq (memB z acc) false -> Eq (E z) true)
         -> IFin E -> List Val
reachFind : (ws : List Val) (G : Val -> Val -> Bool) (v : Val) {E : Val -> Bool}
            (acc : List Val)
         -> ((z : Val) -> Mem z ws -> Eq (memB z acc) false -> Eq (E z) true)
         -> IFin E -> FindResult (rOk G v acc) ws -> List Val

reachGo ws G v acc av bar = reachFind ws G v acc av bar (findFalse (rOk G v acc) ws)

reachFind ws G v acc av bar          (allT f)      = acc
reachFind ws G v {E} acc av (cBar h) (found x m q) =
  reachGo ws G v (rAdd ws G v acc) av' (h x (av x m (rOutAcc G v acc x q)))
  where
    av' : (z : Val) -> Mem z ws -> Eq (memB z (rAdd ws G v acc)) false
       -> Eq (boolAnd (E z) (neqB x z)) true
    av' z mz e =
      andIntro (E z) (neqB x z)
               (av z mz (outAcc (memB z acc) refl))
               (eqCong boolNot (outX (valEq x z) refl))
      where
        outAcc : (b : Bool) -> Eq (memB z acc) b -> Eq (memB z acc) false
        outAcc false eb = eb
        outAcc true  eb =
          emptyElim (memB_false z (rAdd ws G v acc) e
                      (memAppR (filterL (rMiss G v acc) ws) acc
                               (memB_sound z acc eb)))

        outX : (b : Bool) -> Eq (valEq x z) b -> Eq (valEq x z) false
        outX false eb = eb
        outX true  eb =
          emptyElim (memB_false z (rAdd ws G v acc) e
                      (eqSubst (\ y -> Mem y (rAdd ws G v acc)) (valEq_sound x z eb)
                               (rInAdd ws G v acc x m q)))

------------------------------------------------------------------------
-- Its four properties, each by the same recursion.
--
-- The result lies in ws; every member of it is reached by a trail; v is in it;
-- and it is closed under G-successors inside ws.  The last two are the stopping
-- condition read off, and together they are completeness.

reachGoIn   : (ws : List Val) (G : Val -> Val -> Bool) (v : Val) {E : Val -> Bool}
              (acc : List Val)
           -> (av : (z : Val) -> Mem z ws -> Eq (memB z acc) false -> Eq (E z) true)
           -> (bar : IFin E)
           -> ((z : Val) -> Mem z acc -> Mem z ws)
           -> {z : Val} -> Mem z (reachGo ws G v acc av bar) -> Mem z ws
reachFindIn : (ws : List Val) (G : Val -> Val -> Bool) (v : Val) {E : Val -> Bool}
              (acc : List Val)
           -> (av : (z : Val) -> Mem z ws -> Eq (memB z acc) false -> Eq (E z) true)
           -> (bar : IFin E) (fr : FindResult (rOk G v acc) ws)
           -> ((z : Val) -> Mem z acc -> Mem z ws)
           -> {z : Val} -> Mem z (reachFind ws G v acc av bar fr) -> Mem z ws

reachGoIn ws G v acc av bar = reachFindIn ws G v acc av bar (findFalse (rOk G v acc) ws)

reachFindIn ws G v acc av bar          (allT f)      sb {z} m = sb z m
reachFindIn ws G v acc av (cBar h) (found x mx q) sb    m =
  reachGoIn ws G v (rAdd ws G v acc) _ (h x (av x mx (rOutAcc G v acc x q))) sb' m
  where
    sb' : (z : Val) -> Mem z (rAdd ws G v acc) -> Mem z ws
    sb' z mz = sumElim (\ m1 -> filter_sub (rMiss G v acc) ws m1)
                       (\ m2 -> sb z m2)
                       (memAppCase (filterL (rMiss G v acc) ws) acc mz)

-- Every vertex a round adds is reached by a trail: it is v, or it is a
-- successor of a member of acc, and then the trail of that member grows by one
-- step.

addReaches : (ws : List Val) (G : Val -> Val -> Bool) (v : Val) (acc : List Val)
          -> ((z : Val) -> Mem z acc -> Reaches ws G v z)
          -> (z : Val) -> Mem z (rAdd ws G v acc) -> Reaches ws G v z
addReaches ws G v acc rc z m =
  sumElim fromNew (\ m2 -> rc z m2)
          (memAppCase (filterL (rMiss G v acc) ws) acc m)
  where
    fromNew : Mem z (filterL (rMiss G v acc) ws) -> Reaches ws G v z
    fromNew m1 = sumElim isV viaY (orTrue (valEq v z) (anyL (\ y -> G y z) acc) want)
      where
        mzw : Mem z ws
        mzw = filter_sub (rMiss G v acc) ws m1

        want : Eq (rWant G v acc z) true
        want = andTrueL (rWant G v acc z) (boolNot (memB z acc))
                        (filter_prop (rMiss G v acc) ws m1)

        isV : Eq (valEq v z) true -> Reaches ws G v z
        isV ev = eqSubst (\ y -> Reaches ws G v y) (valEq_sound v z ev)
                         (reachesBy [] tNil)

        viaY : Eq (anyL (\ y -> G y z) acc) true -> Reaches ws G v z
        viaY ea = pick (anyL_true (\ y -> G y z) acc ea)
          where
            pick : Sigma Val (\ y -> Prod (Mem y acc) (Eq (G y z) true))
                -> Reaches ws G v z
            pick (sig y (prod my gy)) = ext (rc y my)
              where
                ext : Reaches ws G v y -> Reaches ws G v z
                ext (reachesBy zs t) =
                  reachesBy (append zs (z :: [])) (trailApp ws G t (tCons mzw gy tNil))

reachGoTrail   : (ws : List Val) (G : Val -> Val -> Bool) (v : Val) {E : Val -> Bool}
                 (acc : List Val)
              -> (av : (z : Val) -> Mem z ws -> Eq (memB z acc) false -> Eq (E z) true)
              -> (bar : IFin E)
              -> ((z : Val) -> Mem z acc -> Reaches ws G v z)
              -> {z : Val} -> Mem z (reachGo ws G v acc av bar) -> Reaches ws G v z
reachFindTrail : (ws : List Val) (G : Val -> Val -> Bool) (v : Val) {E : Val -> Bool}
                 (acc : List Val)
              -> (av : (z : Val) -> Mem z ws -> Eq (memB z acc) false -> Eq (E z) true)
              -> (bar : IFin E) (fr : FindResult (rOk G v acc) ws)
              -> ((z : Val) -> Mem z acc -> Reaches ws G v z)
              -> {z : Val} -> Mem z (reachFind ws G v acc av bar fr) -> Reaches ws G v z

reachGoTrail ws G v acc av bar =
  reachFindTrail ws G v acc av bar (findFalse (rOk G v acc) ws)

reachFindTrail ws G v acc av bar          (allT f)      rc {z} m = rc z m
reachFindTrail ws G v acc av (cBar h) (found x mx q) rc    m =
  reachGoTrail ws G v (rAdd ws G v acc) _ (h x (av x mx (rOutAcc G v acc x q)))
               (addReaches ws G v acc rc) m

reachGoSeed   : (ws : List Val) (G : Val -> Val -> Bool) (v : Val) {E : Val -> Bool}
                (acc : List Val)
             -> (av : (z : Val) -> Mem z ws -> Eq (memB z acc) false -> Eq (E z) true)
             -> (bar : IFin E)
             -> Mem v ws -> Mem v (reachGo ws G v acc av bar)
reachFindSeed : (ws : List Val) (G : Val -> Val -> Bool) (v : Val) {E : Val -> Bool}
                (acc : List Val)
             -> (av : (z : Val) -> Mem z ws -> Eq (memB z acc) false -> Eq (E z) true)
             -> (bar : IFin E) (fr : FindResult (rOk G v acc) ws)
             -> Mem v ws -> Mem v (reachFind ws G v acc av bar fr)

reachGoSeed ws G v acc av bar =
  reachFindSeed ws G v acc av bar (findFalse (rOk G v acc) ws)

reachFindSeed ws G v acc av bar          (allT f)      mv =
  memB_sound v acc
    (notFalse (memB v acc)
              (missTrue (rWant G v acc v) (boolNot (memB v acc)) (f mv)
                        (orL (valEq v v) (anyL (\ y -> G y v) acc) (valEq_refl v))))
reachFindSeed ws G v acc av (cBar h) (found x mx q) mv =
  reachGoSeed ws G v (rAdd ws G v acc) _ (h x (av x mx (rOutAcc G v acc x q))) mv

reachGoClosed   : (ws : List Val) (G : Val -> Val -> Bool) (v : Val) {E : Val -> Bool}
                  (acc : List Val)
               -> (av : (z : Val) -> Mem z ws -> Eq (memB z acc) false -> Eq (E z) true)
               -> (bar : IFin E) {u w : Val}
               -> Mem u (reachGo ws G v acc av bar) -> Mem w ws -> Eq (G u w) true
               -> Mem w (reachGo ws G v acc av bar)
reachFindClosed : (ws : List Val) (G : Val -> Val -> Bool) (v : Val) {E : Val -> Bool}
                  (acc : List Val)
               -> (av : (z : Val) -> Mem z ws -> Eq (memB z acc) false -> Eq (E z) true)
               -> (bar : IFin E) (fr : FindResult (rOk G v acc) ws) {u w : Val}
               -> Mem u (reachFind ws G v acc av bar fr) -> Mem w ws -> Eq (G u w) true
               -> Mem w (reachFind ws G v acc av bar fr)

reachGoClosed ws G v acc av bar =
  reachFindClosed ws G v acc av bar (findFalse (rOk G v acc) ws)

reachFindClosed ws G v acc av bar      (allT f)      {u} {w} mu mw st =
  memB_sound w acc
    (notFalse (memB w acc)
              (missTrue (rWant G v acc w) (boolNot (memB w acc)) (f mw)
                        (orR (valEq v w) (anyL (\ y -> G y w) acc)
                             (anyL_intro (\ y -> G y w) acc mu st))))
reachFindClosed ws G v acc av (cBar h) (found x mx q) mu mw st =
  reachGoClosed ws G v (rAdd ws G v acc) _ (h x (av x mx (rOutAcc G v acc x q)))
                mu mw st

------------------------------------------------------------------------
-- The reachable set itself

reachAv : (ws : List Val) (z : Val) -> Mem z ws -> Eq (memB z []) false
       -> Eq (memB z ws) true
reachAv ws z mz e = memB_complete z ws mz

noAcc : (ws : List Val) (z : Val) -> Mem z ([] {A = Val}) -> Mem z ws
noAcc ws z ()

noAccR : (ws : List Val) (G : Val -> Val -> Bool) (v : Val) (z : Val)
      -> Mem z ([] {A = Val}) -> Reaches ws G v z
noAccR ws G v z ()

reachSet : List Val -> (Val -> Val -> Bool) -> Val -> List Val
reachSet ws G v = reachGo ws G v [] (reachAv ws) (listBar ws)

reachIn : (ws : List Val) (G : Val -> Val -> Bool) (v : Val) {z : Val}
       -> Mem z (reachSet ws G v) -> Mem z ws
reachIn ws G v = reachGoIn ws G v [] (reachAv ws) (listBar ws) (noAcc ws)

reachTrail : (ws : List Val) (G : Val -> Val -> Bool) (v : Val) {z : Val}
          -> Mem z (reachSet ws G v) -> Reaches ws G v z
reachTrail ws G v = reachGoTrail ws G v [] (reachAv ws) (listBar ws) (noAccR ws G v)

reachSeed : (ws : List Val) (G : Val -> Val -> Bool) (v : Val)
         -> Mem v ws -> Mem v (reachSet ws G v)
reachSeed ws G v = reachGoSeed ws G v [] (reachAv ws) (listBar ws)

reachClosed : (ws : List Val) (G : Val -> Val -> Bool) (v : Val) {u w : Val}
           -> Mem u (reachSet ws G v) -> Mem w ws -> Eq (G u w) true
           -> Mem w (reachSet ws G v)
reachClosed ws G v = reachGoClosed ws G v [] (reachAv ws) (listBar ws)

-- Completeness: a trail from a member of the set stays in the set.  This is the
-- half that would have needed the pigeonhole if the search had been run for a
-- fixed number of rounds; here it is an induction along the trail against the
-- stopping condition.

reachTrailIn : (ws : List Val) (G : Val -> Val -> Bool) (v : Val)
               {u : Val} {zs : List Val} {w : Val}
            -> Mem u (reachSet ws G v) -> Trail ws G u zs w -> Mem w (reachSet ws G v)
reachTrailIn ws G v mu tNil                   = mu
reachTrailIn ws G v mu (tCons {x = x} mx e t) =
  reachTrailIn ws G v (reachClosed ws G v mu mx e) t

reachComplete : (ws : List Val) (G : Val -> Val -> Bool) (v : Val) -> Mem v ws
             -> {zs : List Val} {w : Val} -> Trail ws G v zs w
             -> Mem w (reachSet ws G v)
reachComplete ws G v mv t = reachTrailIn ws G v (reachSeed ws G v mv) t

reachTrans : (ws : List Val) (G : Val -> Val -> Bool) (v u w : Val)
          -> Mem u (reachSet ws G v) -> Mem w (reachSet ws G u)
          -> Mem w (reachSet ws G v)
reachTrans ws G v u w mu mw = onR (reachTrail ws G u mw)
  where
    onR : Reaches ws G u w -> Mem w (reachSet ws G v)
    onR (reachesBy zs t) = reachTrailIn ws G v mu t

reachB : List Val -> (Val -> Val -> Bool) -> Val -> Val -> Bool
reachB ws G v w = memB w (reachSet ws G v)

------------------------------------------------------------------------
-- Components, without component objects.
--
-- sccOf ws G r is the strongly connected component of r: the vertices r reaches
-- that reach r back.  It is a filterL of a list, nothing more; there is no
-- quotient, no set of sets, and no equality of components anywhere below.

sccOf : List Val -> (Val -> Val -> Bool) -> Val -> List Val
sccOf ws G r = filterL (\ w -> reachB ws G w r) (reachSet ws G r)

sccReach : (ws : List Val) (G : Val -> Val -> Bool) (r : Val) (w : Val)
        -> Mem w (sccOf ws G r) -> Mem w (reachSet ws G r)
sccReach ws G r w m = filter_sub (\ z -> reachB ws G z r) (reachSet ws G r) m

sccIn : (ws : List Val) (G : Val -> Val -> Bool) (r : Val) (w : Val)
     -> Mem w (sccOf ws G r) -> Mem w ws
sccIn ws G r w m = reachIn ws G r (sccReach ws G r w m)

sccTo : (ws : List Val) (G : Val -> Val -> Bool) (r : Val) (w : Val)
     -> Mem w (sccOf ws G r) -> Reaches ws G r w
sccTo ws G r w m = reachTrail ws G r (sccReach ws G r w m)

sccFrom : (ws : List Val) (G : Val -> Val -> Bool) (r : Val) (w : Val)
       -> Mem w (sccOf ws G r) -> Reaches ws G w r
sccFrom ws G r w m =
  reachTrail ws G w
    (memB_sound r (reachSet ws G w)
      (filter_prop (\ z -> reachB ws G z r) (reachSet ws G r) m))

sccRep : (ws : List Val) (G : Val -> Val -> Bool) (r : Val)
      -> Mem r ws -> Mem r (sccOf ws G r)
sccRep ws G r mr =
  filter_true (\ z -> reachB ws G z r) (reachSet ws G r) (reachSeed ws G r mr)
              (memB_complete r (reachSet ws G r) (reachSeed ws G r mr))

------------------------------------------------------------------------
-- Terminal components.
--
-- r's component is terminal when everything r reaches reaches r back, i.e. when
-- the reachable set of r IS its component.  That is one boolean, and it is the
-- only thing said about the condensation: no edge of it is ever built.

termB : List Val -> (Val -> Val -> Bool) -> Val -> Bool
termB ws G r = allB (\ w -> reachB ws G w r) (reachSet ws G r)

termScc : (ws : List Val) (G : Val -> Val -> Bool) (r : Val)
       -> Eq (termB ws G r) true
       -> {w : Val} -> Mem w (reachSet ws G r) -> Mem w (sccOf ws G r)
termScc ws G r et {w} m =
  filter_true (\ z -> reachB ws G z r) (reachSet ws G r) m
              (allB_at (\ z -> reachB ws G z r) (reachSet ws G r) m et)

-- A terminal component is closed under successors inside ws.  This is what the
-- refutation branch needs of it, and it is the whole use of terminality.

termClosed : (ws : List Val) (G : Val -> Val -> Bool) (r : Val)
          -> Eq (termB ws G r) true
          -> (z y : Val) -> Mem z (sccOf ws G r) -> Mem y ws -> Eq (G z y) true
          -> Mem y (sccOf ws G r)
termClosed ws G r et z y mz my e =
  termScc ws G r et (reachClosed ws G r (sccReach ws G r z mz) my e)

------------------------------------------------------------------------
-- A non-empty graph has a terminal component.
--
-- Follow condensation edges: while r's component is not terminal there is a w
-- that r reaches and that does not reach r, so w's component is strictly later,
-- and one moves the representative to w.  The plan's "acyclicity makes the
-- components visited distinct" is here a Bar search, and the invariant that
-- makes it one is a single hypothesis --
--
--   every vertex of the current reachable set still satisfies the Bar predicate
--
-- -- with no list of visited representatives.  Giving up r is the sub-Bar cBar
-- hands over, and the new reachable set avoids r because w does not reach r.

data TermRes (ws : List Val) (G : Val -> Val -> Bool) : Set where
  termRes : (r : Val) -> Mem r ws -> Eq (termB ws G r) true -> TermRes ws G

termGo   : (ws : List Val) (G : Val -> Val -> Bool) (r : Val) -> Mem r ws
        -> {E : Val -> Bool}
        -> ((z : Val) -> Mem z (reachSet ws G r) -> Eq (E z) true)
        -> IFin E -> TermRes ws G
termFind : (ws : List Val) (G : Val -> Val -> Bool) (r : Val) -> Mem r ws
        -> {E : Val -> Bool}
        -> ((z : Val) -> Mem z (reachSet ws G r) -> Eq (E z) true)
        -> IFin E -> FindResult (\ w -> reachB ws G w r) (reachSet ws G r)
        -> TermRes ws G

termGo ws G r mr av bar =
  termFind ws G r mr av bar (findFalse (\ w -> reachB ws G w r) (reachSet ws G r))

termFind ws G r mr av bar          (allT f)       =
  termRes r mr (allB_intro (\ w -> reachB ws G w r) (reachSet ws G r) f)
termFind ws G r mr {E} av (cBar h) (found w mw q) =
  termGo ws G w (reachIn ws G r mw) av' (h r (av r (reachSeed ws G r mr)))
  where
    av' : (z : Val) -> Mem z (reachSet ws G w) -> Eq (boolAnd (E z) (neqB r z)) true
    av' z mz =
      andIntro (E z) (neqB r z)
               (av z (reachTrans ws G r w z mw mz))
               (eqCong boolNot (notR (valEq r z) refl))
      where
        notR : (b : Bool) -> Eq (valEq r z) b -> Eq (valEq r z) false
        notR false eb = eb
        notR true  eb = emptyElim (tfAbs (eqTrans (eqSym rIn) q))
          where
            rIn : Eq (memB r (reachSet ws G w)) true
            rIn = memB_complete r (reachSet ws G w)
                    (eqSubst (\ y -> Mem y (reachSet ws G w))
                             (eqSym (valEq_sound r z eb)) mz)

findTerm : (ws : List Val) (G : Val -> Val -> Bool) (r : Val) -> Mem r ws
        -> TermRes ws G
findTerm ws G r mr =
  termGo ws G r mr (\ z mz -> memB_complete z ws (reachIn ws G r mz)) (listBar ws)

------------------------------------------------------------------------
-- The positive certificate: a fair circuit.
--
-- A circuit at r is a non-empty closed trail through r together with, for every
-- fairness predicate, a witness on it.  This is the constructive half of the
-- lecture's argument -- pick a witness in each F_i and join them by paths inside
-- the component -- and it is done here rather than in G38, so that G38 has only
-- to reread a Trail as a Walk.

data Circuit (ws : List Val) (G : Val -> Val -> Bool) (fs : List (Val -> Bool))
             (r : Val) : Set where
  circuit : (cy : List Val) -> Trail ws G r cy r -> Eq (nullB cy) false
         -> ((f : Val -> Bool) -> Mem f fs
               -> Sigma Val (\ z -> Prod (Mem z cy) (Eq (f z) true)))
         -> Circuit ws G fs r

circMono : (ws vs : List Val) (G : Val -> Val -> Bool) (fs : List (Val -> Bool))
           (r : Val) -> ((z : Val) -> Mem z ws -> Mem z vs)
        -> Circuit ws G fs r -> Circuit vs G fs r
circMono ws vs G fs r sb (circuit cy t nn wit) =
  circuit cy (trailMono ws vs G sb t) nn wit

fairB : List (Val -> Bool) -> List Val -> Bool
fairB fs C = allB (\ g -> anyL g C) fs

data Loop (ws : List Val) (G : Val -> Val -> Bool) (r : Val) : Set where
  loopBy : (cy : List Val) -> Trail ws G r cy r -> Eq (nullB cy) false -> Loop ws G r

-- A terminal component of a vertex that has a successor is non-trivial.  This
-- is the only place the "every vertex has an out-edge" branch is used, and it
-- is why no separate cycle detection is needed: the successor is reached, so
-- terminality sends a trail back.

loopAt : (ws : List Val) (G : Val -> Val -> Bool) (r : Val) -> Mem r ws
      -> Eq (termB ws G r) true -> Eq (hasOut ws G r) true -> Loop ws G r
loopAt ws G r mr et ho =
  pick (nullB_false (outs ws G r) (notTrue (nullB (outs ws G r)) ho))
  where
    pick : Sigma Val (\ x -> Mem x (outs ws G r)) -> Loop ws G r
    pick (sig x mx) = back (sccFrom ws G r x (termScc ws G r et inR))
      where
        mxw : Mem x ws
        mxw = filter_sub (G r) ws mx

        grx : Eq (G r x) true
        grx = filter_prop (G r) ws mx

        inR : Mem x (reachSet ws G r)
        inR = reachClosed ws G r (reachSeed ws G r mr) mxw grx

        back : Reaches ws G x r -> Loop ws G r
        back (reachesBy zs t) = loopBy (x :: zs) (tCons mxw grx t) refl

-- One fairness predicate added to a circuit.  The leg is  loop ++ (r to w) ++
-- (w to r) , with the loop in front so that the r-to-w half is non-empty and w
-- is therefore a vertex the leg VISITS, not merely an endpoint.  trailApp is
-- left-nested for the same reason associativity never appears.

consCirc : (ws : List Val) (G : Val -> Val -> Bool) (r : Val)
        -> (cy0 : List Val) -> Trail ws G r cy0 r -> Eq (nullB cy0) false
        -> (f : Val -> Bool) (w : Val) -> Eq (f w) true
        -> Reaches ws G r w -> Reaches ws G w r
        -> (fs : List (Val -> Bool)) -> Circuit ws G fs r
        -> Circuit ws G (f :: fs) r
consCirc ws G r cy0 t0 nn f w fw (reachesBy as ta) (reachesBy bs tb) fs
         (circuit cy t nnc wit) =
  circuit (append leg cy) (trailApp ws G legT t) (appNotNull leg cy legNN) each
  where
    front : List Val
    front = append cy0 as

    frontT : Trail ws G r front w
    frontT = trailApp ws G t0 ta

    frontNN : Eq (nullB front) false
    frontNN = appNotNull cy0 as nn

    leg : List Val
    leg = append front bs

    legT : Trail ws G r leg r
    legT = trailApp ws G frontT tb

    legNN : Eq (nullB leg) false
    legNN = appNotNull front bs frontNN

    mw : Mem w leg
    mw = memAppL front bs (trailLast ws G frontT frontNN)

    each : (g : Val -> Bool) -> Mem g (f :: fs)
        -> Sigma Val (\ z -> Prod (Mem z (append leg cy)) (Eq (g z) true))
    each g memHd     = sig w (prod (memAppL leg cy mw) fw)
    each g (memTl m) = shift (wit g m)
      where
        shift : Sigma Val (\ z -> Prod (Mem z cy) (Eq (g z) true))
             -> Sigma Val (\ z -> Prod (Mem z (append leg cy)) (Eq (g z) true))
        shift (sig z (prod mz gz)) = sig z (prod (memAppR leg cy mz) gz)

mkCirc : (ws : List Val) (G : Val -> Val -> Bool) (r : Val)
      -> (cy0 : List Val) -> Trail ws G r cy0 r -> Eq (nullB cy0) false
      -> (C : List Val)
      -> ((u : Val) -> Mem u C -> Reaches ws G r u)
      -> ((u : Val) -> Mem u C -> Reaches ws G u r)
      -> (fs : List (Val -> Bool)) -> Eq (fairB fs C) true
      -> Circuit ws G fs r
mkCirc ws G r cy0 t0 nn C to from []        e = circuit cy0 t0 nn noF
  where
    noF : (f : Val -> Bool) -> Mem f []
       -> Sigma Val (\ z -> Prod (Mem z cy0) (Eq (f z) true))
    noF f ()
mkCirc ws G r cy0 t0 nn C to from (f :: fs) e =
  pick (anyL_true f C (andTrueL (anyL f C) (fairB fs C) e))
  where
    rest : Circuit ws G fs r
    rest = mkCirc ws G r cy0 t0 nn C to from fs (andTrueR (anyL f C) (fairB fs C) e)

    pick : Sigma Val (\ w -> Prod (Mem w C) (Eq (f w) true))
        -> Circuit ws G (f :: fs) r
    pick (sig w (prod mw fw)) =
      consCirc ws G r cy0 t0 nn f w fw (to w mw) (from w mw) fs rest

------------------------------------------------------------------------
-- One step of the outer iteration, decided.
--
-- Given that every vertex of ws has an out-edge: ws is empty, or its terminal
-- component is fair and a circuit is built, or it misses some f and is a block
-- to be refuted.  Nothing here recurses, which is what keeps the outer
-- recursion below down to the shape of elimGo.

data Block (ws : List Val) (G : Val -> Val -> Bool) (fs : List (Val -> Bool)) : Set where
  bEmpty  : Eq (nullB ws) true -> Block ws G fs
  bFair   : (r : Val) -> Mem r ws -> Circuit ws G fs r -> Block ws G fs
  bUnfair : (r : Val) -> Mem r ws -> Eq (termB ws G r) true
         -> (f : Val -> Bool) -> Mem f fs -> Eq (anyL f (sccOf ws G r)) false
         -> Block ws G fs

blockOf : (ws : List Val) (G : Val -> Val -> Bool) (fs : List (Val -> Bool))
       -> ({x : Val} -> Mem x ws -> Eq (hasOut ws G x) true)
       -> TermRes ws G -> Block ws G fs
blockOf ws G fs h (termRes r mr et) = onFair (fairB fs (sccOf ws G r)) refl
  where
    onFair : (b : Bool) -> Eq (fairB fs (sccOf ws G r)) b -> Block ws G fs
    onFair true  eb = fromLoop (loopAt ws G r mr et (h mr))
      where
        fromLoop : Loop ws G r -> Block ws G fs
        fromLoop (loopBy cy t nn) =
          bFair r mr (mkCirc ws G r cy t nn (sccOf ws G r)
                             (sccTo ws G r) (sccFrom ws G r) fs eb)
    onFair false eb = unf (allB_false (\ g -> anyL g (sccOf ws G r)) fs eb)
      where
        unf : Sigma (Val -> Bool)
                    (\ g -> Prod (Mem g fs) (Eq (anyL g (sccOf ws G r)) false))
           -> Block ws G fs
        unf (sig g (prod mg eg)) = bUnfair r mr et g mg eg

pickBlock : (ws : List Val) (G : Val -> Val -> Bool) (fs : List (Val -> Bool))
         -> ({x : Val} -> Mem x ws -> Eq (hasOut ws G x) true) -> Block ws G fs
pickBlock []       G fs h = bEmpty refl
pickBlock (u :: ws) G fs h =
  blockOf (u :: ws) G fs h (findTerm (u :: ws) G u memHd)

------------------------------------------------------------------------
-- The negative certificate.
--
-- A well-founded record of the removal order, indexed by what is LEFT.  Two
-- kinds of step, and they are the two cases of Theorem 4.1 of m4.tex with the
-- formulas taken out: a vertex with no out-edge inside ws, and a block closed
-- under out-edges inside ws that misses a fairness predicate.  cNil says
-- nothing is left, so certAll below concludes about every vertex.

dropV : Val -> List Val -> List Val
dropV x ws = filterL (neqB x) ws

dropL : List Val -> List Val -> List Val
dropL C ws = filterL (\ z -> boolNot (memB z C)) ws

data Cert (G : Val -> Val -> Bool) (fs : List (Val -> Bool)) : List Val -> Set where
  cNil   : (ws : List Val) -> Eq (nullB ws) true -> Cert G fs ws
  cSink  : (ws : List Val) (x : Val) -> Mem x ws
        -> Eq (nullB (outs ws G x)) true
        -> Cert G fs (dropV x ws) -> Cert G fs ws
  cBlock : (ws C : List Val) (f : Val -> Bool) -> Mem f fs
        -> ((z : Val) -> Mem z C -> Mem z ws)
        -> ((z y : Val) -> Mem z C -> Mem y ws -> Eq (G z y) true -> Mem y C)
        -> ((z : Val) -> Mem z C -> Eq (f z) false)
        -> Cert G fs (dropL C ws) -> Cert G fs ws

------------------------------------------------------------------------
-- The theorem, on a sub-list

data FairIn (ws : List Val) (G : Val -> Val -> Bool) (fs : List (Val -> Bool)) : Set where
  fairIn : (r : Val) -> Mem r ws -> Circuit ws G fs r -> FairIn ws G fs

fairInMono : (ws vs : List Val) (G : Val -> Val -> Bool) (fs : List (Val -> Bool))
          -> ((z : Val) -> Mem z ws -> Mem z vs)
          -> FairIn ws G fs -> FairIn vs G fs
fairInMono ws vs G fs sb (fairIn r mr c) =
  fairIn r (sb r mr) (circMono ws vs G fs r sb c)

-- Terminal-component removal.  A REMOVING iteration, so barRec covers it and
-- there is no rank and no topological sort: whichever of the two steps applies,
-- the vertex it names leaves ws and leaves the Bar's predicate with it, which is
-- what dropInE says.  For the sink that vertex is x; for a block it is the
-- representative r, which lies in its own component by sccRep.

graphGo   : (G : Val -> Val -> Bool) (fs : List (Val -> Bool)) {E : Val -> Bool}
            (ws : List Val) -> InE E ws -> IFin E
         -> Sum (FairIn ws G fs) (Cert G fs ws)
graphFind : (G : Val -> Val -> Bool) (fs : List (Val -> Bool)) {E : Val -> Bool}
            (ws : List Val) -> InE E ws -> IFin E
         -> FindResult (hasOut ws G) ws
         -> Sum (FairIn ws G fs) (Cert G fs ws)
graphBlk  : (G : Val -> Val -> Bool) (fs : List (Val -> Bool)) {E : Val -> Bool}
            (ws : List Val) -> InE E ws -> IFin E
         -> Block ws G fs -> Sum (FairIn ws G fs) (Cert G fs ws)

graphGo G fs ws sb bar = graphFind G fs ws sb bar (findFalse (hasOut ws G) ws)

graphFind G fs ws sb bar      (allT f)       =
  graphBlk G fs ws sb bar (pickBlock ws G fs f)
graphFind G fs ws sb (cBar h) (found x mx q) =
  sumElim (\ fi -> inl (fairInMono (dropV x ws) ws G fs
                                   (\ z m -> filter_sub (neqB x) ws m) fi))
          (\ c  -> inr (cSink ws x mx (notFalse (nullB (outs ws G x)) q) c))
          (graphGo G fs (dropV x ws) (dropInE (neqB x) ws sb x (neqB_self x))
                   (h x (sb x mx)))

graphBlk G fs ws sb bar      (bEmpty e)                 = inr (cNil ws e)
graphBlk G fs ws sb bar      (bFair r mr c)             = inl (fairIn r mr c)
graphBlk G fs ws sb (cBar h) (bUnfair r mr et g mg eg) =
  sumElim (\ fi -> inl (fairInMono (dropL C ws) ws G fs
                                   (\ z m -> filter_sub (\ y -> boolNot (memB y C)) ws m)
                                   fi))
          (\ c  -> inr (cBlock ws C g mg (sccIn ws G r) (termClosed ws G r et) miss c))
          (graphGo G fs (dropL C ws)
                   (dropInE (\ y -> boolNot (memB y C)) ws sb r
                            (eqCong boolNot (memB_complete r C (sccRep ws G r mr))))
                   (h r (sb r mr)))
  where
    C : List Val
    C = sccOf ws G r

    miss : (z : Val) -> Mem z C -> Eq (g z) false
    miss z mz = anyL_false g C eg mz

------------------------------------------------------------------------
-- The theorem

data FairLoop (vs : List Val) (G : Val -> Val -> Bool) (fs : List (Val -> Bool))
              (v : Val) : Set where
  fairLoop : (r : Val) (st cy : List Val)
          -> Trail vs G v st r -> Trail vs G r cy r -> Eq (nullB cy) false
          -> ((f : Val -> Bool) -> Mem f fs
                -> Sigma Val (\ z -> Prod (Mem z cy) (Eq (f z) true)))
          -> FairLoop vs G fs v

fairGraph : (vs : List Val) (G : Val -> Val -> Bool) (fs : List (Val -> Bool))
            (v : Val) -> Mem v vs
         -> Sum (FairLoop vs G fs v) (Cert G fs (reachSet vs G v))
fairGraph vs G fs v mv =
  sumElim (\ fi -> inl (toLoop fi)) inr
          (graphGo G fs (reachSet vs G v) (memInE (reachSet vs G v))
                   (listBar (reachSet vs G v)))
  where
    into : (z : Val) -> Mem z (reachSet vs G v) -> Mem z vs
    into z m = reachIn vs G v m

    toLoop : FairIn (reachSet vs G v) G fs -> FairLoop vs G fs v
    toLoop (fairIn r mr c) =
      withStem (reachTrail vs G v mr) (circMono (reachSet vs G v) vs G fs r into c)
      where
        withStem : Reaches vs G v r -> Circuit vs G fs r -> FairLoop vs G fs v
        withStem (reachesBy st ts) (circuit cy t nn wit) = fairLoop r st cy ts t nn wit

------------------------------------------------------------------------
-- What a certificate is FOR.
--
-- Reading the removal order as a well-founded induction.  R is the property to
-- be established of every vertex -- for G39 it is  Deriv (neg (chi P u)) -- and
-- the hypothesis carried is "R holds outside ws", which is Refuted of
-- LTL.Extract verbatim.  The sink case is what extractR1 consumes and the block
-- case is what extractR2 consumes; no formula has to appear for that to be
-- decided here.

certAll : (G : Val -> Val -> Bool) (fs : List (Val -> Bool)) (R : Val -> Set)
       -> ((ws : List Val) (x : Val) -> Mem x ws
             -> Eq (nullB (outs ws G x)) true
             -> ((z : Val) -> Eq (memB z ws) false -> R z) -> R x)
       -> ((ws C : List Val) (f : Val -> Bool) -> Mem f fs
             -> ((z : Val) -> Mem z C -> Mem z ws)
             -> ((z y : Val) -> Mem z C -> Mem y ws -> Eq (G z y) true -> Mem y C)
             -> ((z : Val) -> Mem z C -> Eq (f z) false)
             -> ((z : Val) -> Eq (memB z ws) false -> R z)
             -> (z : Val) -> Mem z C -> R z)
       -> {ws : List Val} -> Cert G fs ws
       -> ((z : Val) -> Eq (memB z ws) false -> R z)
       -> (z : Val) -> R z
certAll G fs R hs hb (cNil ws e)          ih z = ih z (nullMemB ws z e)
certAll G fs R hs hb (cSink ws x mx e c)  ih z = certAll G fs R hs hb c ih' z
  where
    ih' : (y : Val) -> Eq (memB y (dropV x ws)) false -> R y
    ih' y eo = onWs (memB y ws) refl
      where
        onWs : (b : Bool) -> Eq (memB y ws) b -> R y
        onWs false eb = ih y eb
        onWs true  eb = onX (valEq x y) refl
          where
            my : Mem y ws
            my = memB_sound y ws eb

            onX : (c' : Bool) -> Eq (valEq x y) c' -> R y
            onX true  ec = eqSubst R (valEq_sound x y ec) (hs ws x mx e ih)
            onX false ec =
              emptyElim (memB_false y (dropV x ws) eo
                          (filter_true (neqB x) ws my (eqCong boolNot ec)))
certAll G fs R hs hb (cBlock ws C f mf sb cl mis c) ih z =
  certAll G fs R hs hb c ih' z
  where
    ih' : (y : Val) -> Eq (memB y (dropL C ws)) false -> R y
    ih' y eo = onWs (memB y ws) refl
      where
        onWs : (b : Bool) -> Eq (memB y ws) b -> R y
        onWs false eb = ih y eb
        onWs true  eb = onC (memB y C) refl
          where
            my : Mem y ws
            my = memB_sound y ws eb

            onC : (c' : Bool) -> Eq (memB y C) c' -> R y
            onC true  ec = hb ws C f mf sb cl mis ih y (memB_sound y C ec)
            onC false ec =
              emptyElim (memB_false y (dropL C ws) eo
                          (filter_true (\ u -> boolNot (memB u C)) ws my
                                       (eqCong boolNot ec)))

------------------------------------------------------------------------
-- The two outputs are EXCLUSIVE.
--
-- This is the intuitive half of the lecture's argument, and the point is that it
-- comes out FINITARY.  The lecture says "an infinite path eventually stays
-- inside one SCC", which needs an infinite path and a classical step; what is
-- actually needed is the contrapositive about a FINITE cycle, and that is two
-- observations about a closed trail:
--
--   a vertex on a cycle has a successor,  so a sink is on no cycle;
--   any vertex of a cycle reaches any other,  so a cycle that enters a
--     successor-closed block never leaves it.
--
-- Both are inductions on a trail of the length it happens to have.  No infinite
-- path is mentioned, nothing is coinductive, and no pigeonhole is used -- which
-- is the same three absences FORMALISATION-PLAN.md section 4f claims for the
-- rest of the development.

-- The suffix of a trail from any vertex it visits, and the prefix to one.  This
-- is walkFrom of LTL.Walk, in both directions, and it is all the "rotate the
-- cycle" the argument needs.

reachesCons : (ws : List Val) (G : Val -> Val -> Bool) {v x s : Val}
           -> Mem x ws -> Eq (G v x) true -> Reaches ws G x s -> Reaches ws G v s
reachesCons ws G m e (reachesBy zs t) = reachesBy (_ :: zs) (tCons m e t)

reachesApp : (ws : List Val) (G : Val -> Val -> Bool) {u v w : Val}
          -> Reaches ws G u v -> Reaches ws G v w -> Reaches ws G u w
reachesApp ws G (reachesBy as ta) (reachesBy bs tb) =
  reachesBy (append as bs) (trailApp ws G ta tb)

trailFrom : (ws : List Val) (G : Val -> Val -> Bool) {v : Val} {zs : List Val} {w : Val}
         -> Trail ws G v zs w -> {s : Val} -> Mem s (v :: zs) -> Reaches ws G s w
trailFrom ws G tNil          memHd     = reachesBy [] tNil
trailFrom ws G tNil          (memTl ())
trailFrom ws G (tCons m e t) memHd     = reachesBy _ (tCons m e t)
trailFrom ws G (tCons m e t) (memTl k) = trailFrom ws G t k

trailTo : (ws : List Val) (G : Val -> Val -> Bool) {v : Val} {zs : List Val} {w : Val}
       -> Trail ws G v zs w -> {s : Val} -> Mem s zs -> Reaches ws G v s
trailTo ws G tNil          ()
trailTo ws G (tCons m e t) memHd     = reachesBy (_ :: []) (tCons m e tNil)
trailTo ws G (tCons m e t) (memTl k) = reachesCons ws G m e (trailTo ws G t k)

-- Observation one: a vertex on a cycle has a successor inside ws.  Along a
-- trail, every vertex visited has a successor provided the ENDPOINT has, and for
-- a closed trail the endpoint is the start, whose successor is the trail's own
-- first step.

data HasSucc (ws : List Val) (G : Val -> Val -> Bool) (x : Val) : Set where
  hasSucc : (y : Val) -> Mem y ws -> Eq (G x y) true -> HasSucc ws G x

firstStep : (ws : List Val) (G : Val -> Val -> Bool) {v : Val} {zs : List Val} {w : Val}
         -> Trail ws G v zs w -> Eq (nullB zs) false -> HasSucc ws G v
firstStep ws G tNil                  ()
firstStep ws G (tCons {x = y} m e t) nn = hasSucc y m e

headSucc : (ws : List Val) (G : Val -> Val -> Bool) {v : Val} {zs : List Val} {w : Val}
        -> Trail ws G v zs w -> HasSucc ws G w -> HasSucc ws G v
headSucc ws G tNil                  hw = hw
headSucc ws G (tCons {x = y} m e t) hw = hasSucc y m e

trailSucc : (ws : List Val) (G : Val -> Val -> Bool) {v : Val} {zs : List Val} {w : Val}
         -> Trail ws G v zs w -> HasSucc ws G w -> {x : Val} -> Mem x zs -> HasSucc ws G x
trailSucc ws G tNil          hw ()
trailSucc ws G (tCons m e t) hw memHd     = headSucc ws G t hw
trailSucc ws G (tCons m e t) hw (memTl k) = trailSucc ws G t hw k

cycSucc : (ws : List Val) (G : Val -> Val -> Bool) (r : Val) (cy : List Val)
       -> Trail ws G r cy r -> Eq (nullB cy) false
       -> {x : Val} -> Mem x cy -> HasSucc ws G x
cycSucc ws G r cy t nn mx = trailSucc ws G t (firstStep ws G t nn) mx

-- Observation two: any vertex of a cycle reaches any other -- suffix to the
-- base point, then prefix out again -- and a successor-closed block that a
-- trail starts in contains everything the trail reaches.

cycConn : (ws : List Val) (G : Val -> Val -> Bool) (r : Val) (cy : List Val)
       -> Trail ws G r cy r -> (u z : Val) -> Mem u cy -> Mem z cy -> Reaches ws G u z
cycConn ws G r cy t u z mu mz =
  reachesApp ws G (trailFrom ws G t (memTl mu)) (trailTo ws G t mz)

blockAlong : (ws C : List Val) (G : Val -> Val -> Bool)
          -> ((z y : Val) -> Mem z C -> Mem y ws -> Eq (G z y) true -> Mem y C)
          -> {u : Val} {zs : List Val} {z : Val}
          -> Trail ws G u zs z -> Mem u C -> Mem z C
blockAlong ws C G cl tNil                       mu = mu
blockAlong ws C G cl (tCons {x = y} m e t)      mu =
  blockAlong ws C G cl t (cl _ y mu m e)

trailRestrict : (ws vs : List Val) (G : Val -> Val -> Bool)
                {v : Val} {zs : List Val} {w : Val}
             -> Trail ws G v zs w -> ((z : Val) -> Mem z zs -> Mem z vs)
             -> Trail vs G v zs w
trailRestrict ws vs G tNil                 h = tNil
trailRestrict ws vs G (tCons {x = y} m e t) h =
  tCons (h y memHd) e (trailRestrict ws vs G t (\ z mz -> h z (memTl mz)))

-- The theorem: a certificate for ws forbids a fair circuit inside ws.
--
-- Induction on the certificate, and each step says the cycle SURVIVES the
-- removal -- it never touched what was removed -- so the cycle is still there
-- when nothing is left, which cNil forbids.  That is the whole content of "an
-- infinite path eventually stays inside one SCC", finitely.

certNoCirc : (G : Val -> Val -> Bool) (fs : List (Val -> Bool)) {ws : List Val}
          -> Cert G fs ws -> (r : Val) -> Circuit ws G fs r -> Empty
certNoCirc G fs (cNil ws e)         r (circuit cy t nn wit) =
  nullB_mem ws e (trailIn ws G t (trailLast ws G t nn))
certNoCirc G fs (cSink ws x mx e c) r (circuit cy t nn wit) =
  certNoCirc G fs c r (circuit cy (trailRestrict ws (dropV x ws) G t keep) nn wit)
  where
    offCycle : Mem x cy -> Empty
    offCycle m = onS (cycSucc ws G r cy t nn m)
      where
        onS : HasSucc ws G x -> Empty
        onS (hasSucc y my gy) = nullB_mem (outs ws G x) e (filter_true (G x) ws my gy)

    keep : (z : Val) -> Mem z cy -> Mem z (dropV x ws)
    keep z mz = filter_true (neqB x) ws (trailIn ws G t mz) (out (valEq x z) refl)
      where
        out : (b : Bool) -> Eq (valEq x z) b -> Eq (neqB x z) true
        out false eb = eqCong boolNot eb
        out true  eb =
          emptyElim (offCycle (eqSubst (\ y -> Mem y cy)
                                       (eqSym (valEq_sound x z eb)) mz))
certNoCirc G fs (cBlock ws C f mf sb cl mis c) r (circuit cy t nn wit) =
  certNoCirc G fs c r (circuit cy (trailRestrict ws (dropL C ws) G t keep) nn wit)
  where
    inBlock : (z : Val) -> Mem z cy -> Mem z C -> Empty
    inBlock z mz mzc = onW (wit f mf)
      where
        onW : Sigma Val (\ y -> Prod (Mem y cy) (Eq (f y) true)) -> Empty
        onW (sig y (prod my fy)) = tfAbs (eqTrans (eqSym fy) (mis y inC))
          where
            inC : Mem y C
            inC = along (cycConn ws G r cy t z y mz my)
              where
                along : Reaches ws G z y -> Mem y C
                along (reachesBy as ta) = blockAlong ws C G cl ta mzc

    keep : (z : Val) -> Mem z cy -> Mem z (dropL C ws)
    keep z mz = filter_true (\ y -> boolNot (memB y C)) ws (trailIn ws G t mz)
                            (out (memB z C) refl)
      where
        out : (b : Bool) -> Eq (memB z C) b -> Eq (boolNot (memB z C)) true
        out false eb = eqCong boolNot eb
        out true  eb = emptyElim (inBlock z mz (memB_sound z C eb))

------------------------------------------------------------------------
-- The dichotomy, at the top level.
--
-- fairGraph's two answers cannot both be right, and therefore the negative
-- answer is a DECISION: if a fair lasso from v exists at all, fairGraph returns
-- one.  Restricting the lasso's cycle to the reachable set is reachComplete,
-- which is where the growing search of the first half pays off.

gotLoop : {A B : Set} -> Sum A B -> Bool
gotLoop (inl a) = true
gotLoop (inr b) = false

fairNoLoop : (vs : List Val) (G : Val -> Val -> Bool) (fs : List (Val -> Bool))
             (v : Val) -> Mem v vs
          -> Cert G fs (reachSet vs G v) -> FairLoop vs G fs v -> Empty
fairNoLoop vs G fs v mv c (fairLoop r st cy ts t nn wit) =
  certNoCirc G fs c r
             (circuit cy (trailRestrict vs (reachSet vs G v) G t keep) nn wit)
  where
    keep : (z : Val) -> Mem z cy -> Mem z (reachSet vs G v)
    keep z mz = onR (reachesApp vs G (reachesBy st ts) (trailTo vs G t mz))
      where
        onR : Reaches vs G v z -> Mem z (reachSet vs G v)
        onR (reachesBy zs tz) = reachComplete vs G v mv tz

fairComplete : (vs : List Val) (G : Val -> Val -> Bool) (fs : List (Val -> Bool))
               (v : Val) (mv : Mem v vs)
            -> FairLoop vs G fs v -> Eq (gotLoop (fairGraph vs G fs v mv)) true
fairComplete vs G fs v mv fl = onS (fairGraph vs G fs v mv) refl
  where
    onS : (s : Sum (FairLoop vs G fs v) (Cert G fs (reachSet vs G v)))
       -> Eq (fairGraph vs G fs v mv) s
       -> Eq (gotLoop (fairGraph vs G fs v mv)) true
    onS (inl l) es = eqCong gotLoop es
    onS (inr c) es = emptyElim (fairNoLoop vs G fs v mv c fl)

------------------------------------------------------------------------
-- Computational checks.
--
-- Two vertices,  a = 1  and  b = 0 , with every edge pointing at b: a -> b and
-- b -> b.  So b's component is terminal and non-trivial, a's is not terminal,
-- and the answer depends only on which vertex the fairness predicate asks for.

gA : Val
gA = true :: []

gB : Val
gB = false :: []

gVs : List Val
gVs = gA :: gB :: []

gE : Val -> Val -> Bool
gE v w = valEq w gB

reach_gA : Eq (reachSet gVs gE gA) (gB :: gA :: [])
reach_gA = refl

term_gA : Eq (termB gVs gE gA) false
term_gA = refl

term_gB : Eq (termB gVs gE gB) true
term_gB = refl

scc_gB : Eq (sccOf gVs gE gB) (gB :: [])
scc_gB = refl

-- Asking for b is fair: the cycle b -> b meets it.

fair_gB : Eq (gotLoop (fairGraph gVs gE ((\ v -> valEq v gB) :: []) gA memHd)) true
fair_gB = refl

-- Asking for a is not: a is transient, so the only recurrent component misses
-- the predicate and the certificate branch is taken.

fair_gA : Eq (gotLoop (fairGraph gVs gE ((\ v -> valEq v gA) :: []) gA memHd)) false
fair_gA = refl

------------------------------------------------------------------------
-- A second graph, which exercises everything the first does not.
--
--   p -> q ,  q -> s ,  s -> q
--
-- p is transient and {q,s} is a two-vertex recurrent component, so: findTerm
-- has to move the representative once (p's component is not terminal), the
-- circuit has two legs to concatenate rather than none, and on the unfair side
-- the certificate uses all three of its constructors -- cBlock removes {q,s},
-- then cSink removes p, which only becomes a sink once the component is gone,
-- then cNil.

gP : Val
gP = true :: true :: []

gQ : Val
gQ = true :: false :: []

gS : Val
gS = false :: false :: []

gVs2 : List Val
gVs2 = gP :: gQ :: gS :: []

gE2 : Val -> Val -> Bool
gE2 v w = boolOr (boolAnd (valEq v gP) (valEq w gQ))
                 (boolOr (boolAnd (valEq v gQ) (valEq w gS))
                         (boolAnd (valEq v gS) (valEq w gQ)))

term_gP : Eq (termB gVs2 gE2 gP) false
term_gP = refl

term_gQ : Eq (termB gVs2 gE2 gQ) true
term_gQ = refl

scc_gQ : Eq (map (\ z -> memB z (sccOf gVs2 gE2 gQ)) gVs2) (false :: true :: true :: [])
scc_gQ = refl

-- The lasso the fair branch returns, read off in full.
--
-- findTerm settles on s as the representative, so the stem is  p -> q -> s  and
-- the loop is  s -> q -> s .  Two fairness predicates, "is q" and "is s"; the
-- cycle is one leg per predicate followed by the bare loop, each leg being the
-- loop again then out to the witness and back --
--
--   q s q s   for "is q" ,   q s   for "is s" ,   q s   the loop
--
-- and the leg carries the loop in FRONT precisely so that the out-half is
-- non-empty and the witness is therefore a vertex the leg VISITS, not merely an
-- endpoint; for "is s" the out-half and the back-half are both empty, since the
-- witness is the representative, and only the leading loop makes that leg a
-- cycle through s at all.  This is the SCC construction choosing witnesses in
-- its own order, and it is not the shortest fair cycle -- q s would do.

loopCy : {vs : List Val} {G : Val -> Val -> Bool} {fs : List (Val -> Bool)} {v : Val}
      -> FairLoop vs G fs v -> List Val
loopCy (fairLoop r st cy ts t nn wit) = cy

cyOf : {vs : List Val} {G : Val -> Val -> Bool} {fs : List (Val -> Bool)} {v : Val}
    -> Sum (FairLoop vs G fs v) (Cert G fs (reachSet vs G v)) -> List Val
cyOf (inl l) = loopCy l
cyOf (inr c) = []

stemOf : {vs : List Val} {G : Val -> Val -> Bool} {fs : List (Val -> Bool)} {v : Val}
      -> Sum (FairLoop vs G fs v) (Cert G fs (reachSet vs G v)) -> List Val
stemOf (inl (fairLoop r st cy ts t nn wit)) = st
stemOf (inr c)                              = []

fairQS : Sum (FairLoop gVs2 gE2 ((\ v -> valEq v gQ) :: (\ v -> valEq v gS) :: []) gP)
             (Cert gE2 ((\ v -> valEq v gQ) :: (\ v -> valEq v gS) :: [])
                   (reachSet gVs2 gE2 gP))
fairQS = fairGraph gVs2 gE2 ((\ v -> valEq v gQ) :: (\ v -> valEq v gS) :: []) gP memHd

fair_QS : Eq (gotLoop fairQS) true
fair_QS = refl

stem_QS : Eq (stemOf fairQS) (gQ :: gS :: [])
stem_QS = refl

cy_QS : Eq (cyOf fairQS) (gQ :: gS :: gQ :: gS :: gQ :: gS :: gQ :: gS :: [])
cy_QS = refl

-- And the unfair side: nothing recurrent meets "is p".

fair_P : Eq (gotLoop (fairGraph gVs2 gE2 ((\ v -> valEq v gP) :: []) gP memHd)) false
fair_P = refl

-- The certificate it returns instead, as the list of its steps: 2 for cBlock,
-- 1 for cSink, 0 for cNil.  It is  cBlock, cSink, cNil  -- the component {q,s}
-- is refuted first because it misses "is p", and only then is p a sink, which is
-- the whole point of the backwards induction: p is refuted BECAUSE its successor
-- already was.  Reading this off is what certAll does with a formula attached.

certShape : {G : Val -> Val -> Bool} {fs : List (Val -> Bool)} {ws : List Val}
         -> Cert G fs ws -> List Nat
certShape (cNil ws e)                    = 0 :: []
certShape (cSink ws x mx e c)            = 1 :: certShape c
certShape (cBlock ws C f mf sb cl mis c) = 2 :: certShape c

certSteps : {vs : List Val} {G : Val -> Val -> Bool} {fs : List (Val -> Bool)} {v : Val}
       -> Sum (FairLoop vs G fs v) (Cert G fs (reachSet vs G v)) -> List Nat
certSteps (inl l) = []
certSteps (inr c) = certShape c

cert_P : Eq (certSteps (fairGraph gVs2 gE2 ((\ v -> valEq v gP) :: []) gP memHd))
            (2 :: 1 :: 0 :: [])
cert_P = refl
