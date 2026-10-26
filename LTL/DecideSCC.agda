{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.DecideSCC -- G40 of PHASE11-PLAN.md: the two branches joined.
--
--   decideSCC : (Q : Formula) -> Sum (Deriv Q) (LassoCountermodel Q)
--
-- the same type as decide (LTL.Decide, Theorem 6.1), decided by a different
-- question.  decide asks a BOOLEAN of the elimination,
--
--     satB (neg Q)  --  does some surviving state contain neg Q?
--
-- and decideSCC asks which way the graph search went,
--
--     sccGraph (neg Q)  --  is there a fair component in Ust (neg Q)?
--
-- Neither branch is obtained by refuting the other, exactly as in decide: the
-- certificate branch returns a derivation built by G39 and never mentions a
-- lasso, and the fair branch returns a lasso built by G38 and mentions a
-- derivation only to consume one.
--
-- Why the search is run on all of Ust P and not from a vertex.  fairGraph is
-- v-centred and certifies only  reachSet vs G v ; the refutation branch has to
-- account for every state at once, so graphGo over Ust P is what G39 consumes.
-- Asking the question there is legitimate BECAUSE of the first lemma of
-- LTL.SccTrap: every state of Ust P is reached from a state containing P, so a
-- fair component anywhere in Ust P is a fair component reachable from a seed,
-- and the seed is what a countermodel needs.  Without that lemma the fair
-- branch would exhibit a loop that is a countermodel to nothing.
--
-- The route from a fair component to a countermodel, in four steps.
--
--   1. ustSeedTo -- the component's representative r is reached by a trail from
--      a state s with  neg Q  in it.  Stem and cycle together are a FairLoop
--      from s (LTL.Graph), still inside Ust P.
--   2. The loop is restricted to the list of vertices it actually uses,
--      C = s :: stem ++ cycle .  This is where the Trap is built: every vertex
--      of C has a successor in C -- the next one along, and for the cycle's
--      base point its own first step -- and every eventuality pending at a
--      vertex of C fails somewhere reachable inside C, by walking to the
--      witness the graph layer chose and reading evPred there.  Those are the
--      negations of (R1) and (R2).
--   3. uinfTrap -- so C survives the elimination and lies in Uinf P.  This is
--      the step that lets the existing positive tail be used unchanged: sccLasso
--      of G38 takes exactly the inclusion  C subset Uinf P  as its hypothesis,
--      which is why it was stated with that hypothesis rather than at Uinf P.
--   4. sccRun, then buildCMFrom -- Hintikka's lemma at stage 0 and soundness,
--      verbatim from buildCM, with the run supplied rather than built by lasso.
--
-- So the elimination is still COMPUTED in the fair branch -- uinfTrap runs
-- elimGo -- but it is not what decides, and it produces no lasso: the lasso is
-- the SCC construction's.  In the certificate branch the elimination is not
-- computed at all.  That asymmetry is the honest summary of what the phase
-- bought, and checkpoint C8 measures it.

module LTL.DecideSCC where

open import LTL.SccTrap public
open import LTL.Decide  public

------------------------------------------------------------------------
-- Paths out of trails, for the Trap's second field.

trailPath : (P : Formula) (C : List Val) {v : Val} {zs : List Val} {w : Val}
         -> Trail C (step P) v zs w -> Path P C v w
trailPath P C tNil          = pnil
trailPath P C (tCons m e t) = pcons m e (trailPath P C t)

reachPath : (P : Formula) (C : List Val) {v w : Val}
         -> Reaches C (step P) v w -> Path P C v w
reachPath P C (reachesBy zs t) = trailPath P C t

-- Walking from a pending eventuality to a state where it fails.  Along the way
-- either it is already fulfilled -- and the prefix of the trail to that state
-- is the path -- or it is still pending at the far end, where the caller's
-- hypothesis (for us, evWitness at the graph layer's witness) says it fails.

trapFail : (P : Formula) (C : List Val) (A : Formula) -> Mem (box A) (sub P)
        -> (z w : Val) -> Reaches C (step P) z w
        -> Eq (valOf P z (box A)) false
        -> (Eq (valOf P w (box A)) false -> Eq (valOf P w A) false)
        -> Sigma Val (\ y -> Prod (Path P C z y) (Eq (valOf P y A) false))
trapFail P C A mbx z w (reachesBy as t) pd atW =
  sumElim onFul (\ pw -> sig w (prod (trailPath P C t) (atW pw)))
          (walkPersist P C A mbx (trailWalk P C t) pd)
  where
    onFul : Fulfil P A z as
         -> Sigma Val (\ y -> Prod (Path P C z y) (Eq (valOf P y A) false))
    onFul (ful u mu eu) = pathTo u mu eu
      where
        pathTo : (x : Val) -> Mem x (z :: as) -> Eq (valOf P x A) false
              -> Sigma Val (\ y -> Prod (Path P C z y) (Eq (valOf P y A) false))
        pathTo x memHd     e = sig x (prod pnil e)
        pathTo x (memTl m) e =
          sig x (prod (reachPath P C (trailTo C (step P) t m)) e)

------------------------------------------------------------------------
-- A fair loop, cut down to the vertices it uses, with its Trap.

data ScLasso (P : Formula) (v0 : Val) : Set where
  scLasso : (C : List Val) -> Mem v0 C
         -> ((z : Val) -> Mem z C -> Mem z (Ust P))
         -> Trap P C -> FairLoop C (step P) (evPreds P) v0 -> ScLasso P v0

fairScLasso : (P : Formula) (v0 : Val) -> Mem v0 (Ust P)
           -> FairLoop (Ust P) (step P) (evPreds P) v0 -> ScLasso P v0
fairScLasso P v0 mv0 (fairLoop r st cy ts tc nn wit) =
  scLasso C memHd inC (mkTrap succC fulC) (fairLoop r st cy tsC tcC nn wit)
  where
    C : List Val
    C = v0 :: append st cy

    stC : (z : Val) -> Mem z st -> Mem z C
    stC z m = memTl (memAppL st cy m)

    cyC : (z : Val) -> Mem z cy -> Mem z C
    cyC z m = memTl (memAppR st cy m)

    inC : (z : Val) -> Mem z C -> Mem z (Ust P)
    inC z memHd     = mv0
    inC z (memTl m) = sumElim (\ m1 -> trailIn (Ust P) (step P) ts m1)
                              (\ m2 -> trailIn (Ust P) (step P) tc m2)
                              (memAppCase st cy m)

    tsC : Trail C (step P) v0 st r
    tsC = trailRestrict (Ust P) C (step P) ts stC

    tcC : Trail C (step P) r cy r
    tcC = trailRestrict (Ust P) C (step P) tc cyC

    -- (R1) fails on C: the base point steps onto its own cycle, everything on
    -- the cycle inherits that, and everything on the stem steps forward.
    hr : HasSucc C (step P) r
    hr = firstStep C (step P) tcC nn

    toSig : (x : Val) -> HasSucc C (step P) x
         -> Sigma Val (\ y -> Prod (Mem y C) (Eq (step P x y) true))
    toSig x (hasSucc y my e) = sig y (prod my e)

    succC : (z : Val) -> Mem z C
         -> Sigma Val (\ y -> Prod (Mem y C) (Eq (step P z y) true))
    succC z memHd     = toSig z (headSucc C (step P) tsC hr)
    succC z (memTl m) =
      sumElim (\ m1 -> toSig z (trailSucc C (step P) tsC hr m1))
              (\ m2 -> toSig z (cycSucc C (step P) r cy tcC nn m2))
              (memAppCase st cy m)

    -- every vertex reaches every vertex of the cycle, inside C
    reachW : (z : Val) -> Mem z C -> (w : Val) -> Mem w cy
          -> Reaches C (step P) z w
    reachW z memHd     w mw =
      reachesApp C (step P) (trailFrom C (step P) tsC memHd)
                            (trailTo C (step P) tcC mw)
    reachW z (memTl m) w mw =
      sumElim (\ m1 -> reachesApp C (step P) (trailFrom C (step P) tsC (memTl m1))
                                             (trailTo C (step P) tcC mw))
              (\ m2 -> cycConn C (step P) r cy tcC z w m2 mw)
              (memAppCase st cy m)

    -- (R2) fails on C: walk to the witness and read evPred there.
    fulC : (z : Val) -> Mem z C -> (A : Formula) -> Mem A (boxArgs (sub P))
        -> Eq (valOf P z (box A)) false
        -> Sigma Val (\ y -> Prod (Path P C z y) (Eq (valOf P y A) false))
    fulC z mz A mA pd = onW (wit (evPred P A) (evPredsMem P mA))
      where
        onW : Sigma Val (\ w -> Prod (Mem w cy) (Eq (evPred P A w) true))
           -> Sigma Val (\ y -> Prod (Path P C z y) (Eq (valOf P y A) false))
        onW (sig w (prod mw ew)) =
          trapFail P C A (boxArgs_mem (sub P) mA) z w (reachW z mz w mw) pd
                   (evWitness P A w ew)

-- and then the trap survives the elimination, so G38 applies.

scRun : (P : Formula) (v0 : Val) -> ScLasso P v0
     -> Prod (Mem v0 (Uinf P)) (Run P v0)
scRun P v0 (scLasso C mv0 inU tr flC) =
  prod mv0U (sccRun P C intoU v0 mv0U flC)
  where
    intoU : (z : Val) -> Mem z C -> Mem z (Uinf P)
    intoU = uinfTrap P C tr inU

    mv0U : Mem v0 (Uinf P)
    mv0U = intoU v0 mv0

------------------------------------------------------------------------
-- buildCM with the run supplied.
--
-- Verbatim from LTL.Decide's buildCM except that the run is a parameter rather
-- than  runOf ... (lasso ...) .  Everything else -- (S1) at neg Q, Hintikka's
-- lemma at stage 0, soundness -- is the same three lines, and buildCM itself is
-- untouched: C8 needs both procedures in the development at once.

buildCMFrom : (Q : Formula) (v0 : Val) -> Mem v0 (Uinf (neg Q))
           -> Run (neg Q) v0 -> Eq (valOf (neg Q) v0 (neg Q)) true
           -> LassoCountermodel Q
buildCMFrom Q v0 m r ev = countermodel v0 r m evalFalse noDeriv
  where
    valQ : Eq (valOf (neg Q) v0 Q) false
    valQ =
      notTrue (valOf (neg Q) v0 Q)
        (eqTrans (eqSym (boolEq_sound (valOf (neg Q) v0 (neg Q))
                                      (boolNot (valOf (neg Q) v0 Q))
                                      (stateOk (neg Q) v0 m (sub_self (neg Q)))))
                 ev)

    evalFalse : Eq (eval (neg Q) v0 r Q 0) false
    evalFalse =
      eqTrans (eqSym (hintStart (neg Q) v0 r Q (memTl (sub_self Q)))) valQ

    noDeriv : Deriv Q -> Empty
    noDeriv d = tfAbs (eqTrans (eqSym (soundRun (neg Q) v0 r d 0)) evalFalse)

------------------------------------------------------------------------
-- Theorem 6.1, by the SCC route.

decideSCC : (Q : Formula) -> Sum (Deriv Q) (LassoCountermodel Q)
decideSCC Q = sumElim onFair (\ c -> inl (provableSCC Q c)) (sccGraph (neg Q))
  where
    R : Formula
    R = neg Q

    fromRun : (s : Val) -> Eq (valOf R s R) true
           -> Prod (Mem s (Uinf R)) (Run R s)
           -> Sum (Deriv Q) (LassoCountermodel Q)
    fromRun s es (prod mu rn) = inr (buildCMFrom Q s mu rn es)

    onFair : FairIn (Ust R) (step R) (evPreds R)
          -> Sum (Deriv Q) (LassoCountermodel Q)
    onFair (fairIn r mr c) = onCirc c
      where
        onCirc : Circuit (Ust R) (step R) (evPreds R) r
              -> Sum (Deriv Q) (LassoCountermodel Q)
        onCirc (circuit cy tc nn wit) = onSeed (ustSeedTo R r mr)
          where
            onSeed : SeedTo R r -> Sum (Deriv Q) (LassoCountermodel Q)
            onSeed (seedTo s st ms es ts) =
              fromRun s es
                      (scRun R s (fairScLasso R s ms
                                              (fairLoop r st cy ts tc nn wit)))

------------------------------------------------------------------------
-- Checkpoints.
--
-- The two examples LTL.Extract ends with, and the two LTL.Lasso ends with:
-- the valid ones come back as proofs and the invalid ones as countermodels,
-- through the SCC branch each time.  The full agreement with decide, on all
-- forty-six statements of LTL.Examples, is checkpoint C8 and lives in
-- LTL.Compare, so that it is clear which side of the timing rule it is on.

decideSCC_benAri : Eq (isProof (decideSCC benAri)) true
decideSCC_benAri = refl

decideSCC_bnb : Eq (isProof (decideSCC bnb)) true
decideSCC_bnb = refl

decideSCC_diaP : Eq (isProof (decideSCC diaP)) false
decideSCC_diaP = refl
