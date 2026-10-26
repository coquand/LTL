{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.SccTrap -- the two lemmas G40 needs and PHASE11-PLAN.md did not budget
-- for.  Both are about the SEAM between the graph layer and the two sets the
-- existing development is built on, and neither is graph theory or logic: they
-- are the statements that make  Ust P  and  Uinf P  usable from LTL.Graph.
--
-- Why they are needed at all.  The SCC procedure has to run on  Ust P : the
-- refutation branch (G39) is stated against Ust P, and running the search on
-- Uinf P instead would be circular, since Uinf P IS the elimination the phase
-- is supposed to replace.  But the positive branch (G38) delivers into
-- mkLasso, every side condition of which is against Uinf P.  So something has
-- to carry a fair loop found in Ust P down into Uinf P, and something has to
-- say that a component found anywhere in Ust P is reachable from a state that
-- actually contains P -- otherwise the loop is a countermodel to nothing.
--
-- 1. EVERY STATE OF Ust P IS REACHED FROM A SEED.
--
--    Ust P is closeGo's accumulator, and LTL.Closure proves three things about
--    it -- its members are states, it contains the seeds, it is closed -- but
--    not that it contains NOTHING ELSE.  ustSeeded adds the fourth, in the form
--    that is wanted: a trail from a state containing P.  It is the same
--    recursion as the other three and the same one as reachGoTrail of
--    LTL.Graph: a state a round adds is wanted, i.e. is a seed -- and then the
--    empty trail does it -- or is a successor of something already in, and then
--    that thing's trail grows by one step.
--
--    The trail comes out inside StC P, the candidate list, and seedTrail lifts
--    it into Ust P: a trail of STATES starting at a member of Ust P stays in
--    Ust P, by ustClosed at each step.  So no new closure property is needed
--    and LTL.Closure is not touched.
--
-- 2. A TRAP SURVIVES THE ELIMINATION.
--
--    A Trap is a set C in which every state has a successor and every pending
--    eventuality is fulfilled along a path -- exactly the negations of (R1) and
--    (R2), read as a property of a SET rather than of a round.  trapKeep says a
--    trap is kept by one round, and elimGoTrap runs that along elimGo's own
--    recursion, so  C subset Ust P  gives  C subset Uinf P .
--
--    (R2) is where the work is, and it is one line of existing machinery:
--    gfpSound says a member of gfpW fulfils the eventuality nowhere reachable
--    inside us, and the trap supplies a path to a state where it IS fulfilled.
--    That LTL.Gfp states its fixed point against the inductive Path -- rather
--    than against the fuel-bounded reach of LTL.Reach -- is what makes this
--    three lines instead of a development.
--
--    This is the inclusion LTL/SccLasso.agda's header flagged and deferred:
--    "a fair cycle in Ust P has a successor at every state and fulfils every
--    pending eventuality along itself, so it survives every elimination round
--    and lies in Uinf P -- but that inclusion is a greatest-fixed-point
--    induction over elimGo and is not G38".  It is 60 lines, and it is here.
--
-- Note what the second lemma is NOT.  It is not completeness of the
-- elimination and it is not a new fixed-point theory: it is one direction, the
-- one that says the elimination throws nothing useful away, and it is proved by
-- running the existing recursion with an extra invariant.  The other direction
-- -- that Uinf P is itself a trap -- is Lemma 5.1 and has been in LTL.Fix since
-- Phase 5.

module LTL.SccTrap where

open import LTL.SccExtract public

------------------------------------------------------------------------
-- Two list facts, in the shape the two lemmas want.

memNullB : {A : Set} (xs : List A) {x : A} -> Mem x xs -> Eq (nullB xs) false
memNullB []        ()
memNullB (y :: ys) m = refl

anyL_none : {A : Set} (p : A -> Bool) (xs : List A)
         -> ((y : A) -> Mem y xs -> Eq (p y) false) -> Eq (anyL p xs) false
anyL_none p []        h = refl
anyL_none p (y :: ys) h =
  eqSubst (\ b -> Eq (boolOr b (anyL p ys)) false) (eqSym (h y memHd))
          (anyL_none p ys (\ z m -> h z (memTl m)))

orBothFalse : (a b : Bool) -> Eq a false -> Eq b false -> Eq (boolOr a b) false
orBothFalse a b ea eb = eqTrans (eqCong (\ c -> boolOr c b) ea) eb

------------------------------------------------------------------------
-- 1. Every state of Ust P is reached from a state containing P.
--
-- The trail is carried inside StC P, the list closeGo filters; lifting it into
-- Ust P is seedTrail below.

data Seeded (P : Formula) (w : Val) : Set where
  seeded : (s : Val) (zs : List Val)
        -> Mem s (StC P) -> Eq (valOf P s P) true
        -> Trail (StC P) (step P) s zs w -> Seeded P w

-- One round: a state it adds is a seed, or a successor of something already in.

addSeeded : (P : Formula) (acc : List Val)
         -> ((z : Val) -> Mem z acc -> Seeded P z)
         -> (z : Val) -> Mem z (addAll P acc) -> Seeded P z
addSeeded P acc sd z m =
  sumElim fromNew (\ m2 -> sd z m2)
          (memAppCase (filterL (missing P acc) (StC P)) acc m)
  where
    fromNew : Mem z (filterL (missing P acc) (StC P)) -> Seeded P z
    fromNew m1 =
      sumElim isSeed viaU
              (orTrue (valOf P z P) (anyL (\ u -> step P u z) acc) want)
      where
        mzs : Mem z (StC P)
        mzs = filter_sub (missing P acc) (StC P) m1

        want : Eq (wanted P acc z) true
        want = andTrueL (wanted P acc z) (boolNot (memB z acc))
                        (filter_prop (missing P acc) (StC P) m1)

        isSeed : Eq (valOf P z P) true -> Seeded P z
        isSeed e = seeded z [] mzs e tNil

        viaU : Eq (anyL (\ u -> step P u z) acc) true -> Seeded P z
        viaU ea = pick (anyL_true (\ u -> step P u z) acc ea)
          where
            pick : Sigma Val (\ u -> Prod (Mem u acc) (Eq (step P u z) true))
                -> Seeded P z
            pick (sig u (prod mu su)) = ext (sd u mu)
              where
                ext : Seeded P u -> Seeded P z
                ext (seeded s zs ms es t) =
                  seeded s (append zs (z :: [])) ms es
                         (trailApp (StC P) (step P) t (tCons mzs su tNil))

closeGoSeeded   : (P : Formula) {E : Val -> Bool} (acc : List Val)
               -> (av : (z : Val) -> Mem z (StC P) -> Eq (memB z acc) false
                      -> Eq (E z) true)
               -> (bar : IFin E)
               -> ((z : Val) -> Mem z acc -> Seeded P z)
               -> {z : Val} -> Mem z (closeGo P acc av bar) -> Seeded P z
closeFindSeeded : (P : Formula) {E : Val -> Bool} (acc : List Val)
               -> (av : (z : Val) -> Mem z (StC P) -> Eq (memB z acc) false
                      -> Eq (E z) true)
               -> (bar : IFin E) (fr : FindResult (okAcc P acc) (StC P))
               -> ((z : Val) -> Mem z acc -> Seeded P z)
               -> {z : Val} -> Mem z (closeFind P acc av bar fr) -> Seeded P z

closeGoSeeded P acc av bar =
  closeFindSeeded P acc av bar (findFalse (okAcc P acc) (StC P))

closeFindSeeded P acc av bar      (allT f)       sd {z} m = sd z m
closeFindSeeded P acc av (cBar h) (found x mx q) sd     m =
  closeGoSeeded P (addAll P acc) _ (h x (av x mx (notInAcc P acc x q)))
                (addSeeded P acc sd) m

ustSeeded : (P : Formula) {z : Val} -> Mem z (Ust P) -> Seeded P z
ustSeeded P =
  closeGoSeeded P [] (\ z mz e -> stInE P z (stcSt P mz)) (vecBar P) noSd
  where
    noSd : (z : Val) -> Mem z ([] {A = Val}) -> Seeded P z
    noSd z ()

-- A trail of states out of Ust P stays in Ust P.

seedTrail : (P : Formula) {s : Val} {zs : List Val} {w : Val}
         -> Mem s (Ust P) -> Trail (StC P) (step P) s zs w
         -> Trail (Ust P) (step P) s zs w
seedTrail P ms tNil                   = tNil
seedTrail P ms (tCons {x = y} m e t) = tCons my e (seedTrail P my t)
  where
    my : Mem y (Ust P)
    my = ustClosed P ms (stcSt P m) e

data SeedTo (P : Formula) (w : Val) : Set where
  seedTo : (s : Val) (zs : List Val)
        -> Mem s (Ust P) -> Eq (valOf P s P) true
        -> Trail (Ust P) (step P) s zs w -> SeedTo P w

ustSeedTo : (P : Formula) (w : Val) -> Mem w (Ust P) -> SeedTo P w
ustSeedTo P w m = conv (ustSeeded P m)
  where
    conv : Seeded P w -> SeedTo P w
    conv (seeded s zs ms es t) = seedTo s zs mu es (seedTrail P mu t)
      where
        mu : Mem s (Ust P)
        mu = ustSeed P (stcSt P ms) es

------------------------------------------------------------------------
-- 2. Traps.
--
-- The negations of (R1) and (R2), as a property of a set: every state has a
-- successor inside C, and every eventuality pending at a state of C fails
-- somewhere reachable inside C.

data Trap (P : Formula) (C : List Val) : Set where
  mkTrap : ((z : Val) -> Mem z C
              -> Sigma Val (\ y -> Prod (Mem y C) (Eq (step P z y) true)))
        -> ((z : Val) -> Mem z C -> (A : Formula) -> Mem A (boxArgs (sub P))
              -> Eq (valOf P z (box A)) false
              -> Sigma Val (\ y -> Prod (Path P C z y) (Eq (valOf P y A) false)))
        -> Trap P C

pathMono : (P : Formula) (C us : List Val)
        -> ((z : Val) -> Mem z C -> Mem z us)
        -> {v w : Val} -> Path P C v w -> Path P us v w
pathMono P C us sb pnil                   = pnil
pathMono P C us sb (pcons {w = y} m e p) = pcons (sb y m) e (pathMono P C us sb p)

-- One round keeps a trap.  (R1) fails because the successor is in C, hence in
-- us; (R2) fails because gfpSound would make the eventuality hold along the
-- trap's own path to a state where it fails.

trapKeep : (P : Formula) (us C : List Val) -> Trap P C
        -> ((z : Val) -> Mem z C -> Mem z us)
        -> (z : Val) -> Mem z C -> Eq (keep P us (evList P us) z) true
trapKeep P us C (mkTrap hsucc hful) sb z mz =
  eqCong boolNot (orBothFalse (r1 P us z) (r2 P (evList P us) z) e1 e2)
  where
    e1 : Eq (r1 P us z) false
    e1 = onS (hsucc z mz)
      where
        onS : Sigma Val (\ y -> Prod (Mem y C) (Eq (step P z y) true))
           -> Eq (nullB (succs P us z)) false
        onS (sig y (prod my st)) =
          memNullB (succs P us z) (succsIn P us z (sb y my) st)

    e2 : Eq (r2 P (evList P us) z) false
    e2 = anyL_none (badEv P z) (evList P us) each
      where
        each : (g : Ev) -> Mem g (evList P us) -> Eq (badEv P z g) false
        each (prod A W) mg = onPend (valOf P z (box A)) refl
          where
            pr : Prod (Mem A (boxArgs (sub P))) (Eq W (gfpW P us A))
            pr = evList_of P us mg

            notInW : Eq (valOf P z (box A)) false -> Eq (memB z W) false
            notInW ep = onM (memB z W) refl
              where
                onM : (b : Bool) -> Eq (memB z W) b -> Eq (memB z W) false
                onM false em = em
                onM true  em =
                  emptyElim (clash (hful z mz A (prodFst pr) ep))
                  where
                    mzW : Mem z (gfpW P us A)
                    mzW = eqSubst (\ L -> Mem z L) (prodSnd pr)
                                  (memB_sound z W em)

                    clash : Sigma Val (\ y -> Prod (Path P C z y)
                                                   (Eq (valOf P y A) false))
                         -> Empty
                    clash (sig y (prod pa ef)) =
                      tfAbs (eqTrans (eqSym (gfpSound P us A z mzW y
                                                      (pathMono P C us sb pa)))
                                     ef)

            onPend : (b : Bool) -> Eq (valOf P z (box A)) b
                  -> Eq (badEv P z (prod A W)) false
            onPend true  ep =
              eqSubst (\ c -> Eq (boolAnd (boolNot c) (memB z W)) false)
                      (eqSym ep) refl
            onPend false ep =
              eqSubst (\ c -> Eq (boolAnd (boolNot c) (memB z W)) false)
                      (eqSym ep) (notInW ep)

-- and therefore the whole elimination keeps it.  Same recursion as elimGo, one
-- invariant added; this is the "carry a structure that already contains the
-- proof" move of section 4f one more time.

elimGoTrap   : (P : Formula) {E : Val -> Bool} (us : List Val)
               (sb : InE E us) (bar : IFin E)
            -> (C : List Val) -> Trap P C -> ((z : Val) -> Mem z C -> Mem z us)
            -> (z : Val) -> Mem z C -> Mem z (elimGo P us sb bar)
elimFindTrap : (P : Formula) {E : Val -> Bool} (us : List Val)
               (sb : InE E us) (bar : IFin E)
               (fr : FindResult (keep P us (evList P us)) us)
            -> (C : List Val) -> Trap P C -> ((z : Val) -> Mem z C -> Mem z us)
            -> (z : Val) -> Mem z C -> Mem z (elimFind P us sb bar fr)

elimGoTrap P us sb bar =
  elimFindTrap P us sb bar (findFalse (keep P us (evList P us)) us)

elimFindTrap P us sb bar      (allT f)      C tr inc z mz = inc z mz
elimFindTrap P us sb (cBar h) (found x m q) C tr inc z mz =
  elimGoTrap P (elimRound P us)
             (dropInE (keep P us (evList P us)) us sb x q) (h x (sb x m))
             C tr inc' z mz
  where
    inc' : (y : Val) -> Mem y C -> Mem y (elimRound P us)
    inc' y my = filter_true (keep P us (evList P us)) us (inc y my)
                            (trapKeep P us C tr inc y my)

uinfTrap : (P : Formula) (C : List Val) -> Trap P C
        -> ((z : Val) -> Mem z C -> Mem z (Ust P))
        -> (z : Val) -> Mem z C -> Mem z (Uinf P)
uinfTrap P = elimGoTrap P (Ust P) (ustInE P) (ustBar P)
