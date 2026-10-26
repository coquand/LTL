{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.SccExtract -- G39 of PHASE11-PLAN.md: a bad component gives refutations.
--
-- The other half of the translation layer.  G38 read LTL.Graph's positive
-- answer as a lasso; this file reads its NEGATIVE answer -- a Cert, the record
-- of the order in which the vertices were removed -- as Hilbert proofs, through
-- certAll, chi and (Ind).  The result is
--
--     provableSCC : (Q : Formula)
--                -> Cert (step (neg Q)) (evPreds (neg Q)) (Ust (neg Q))
--                -> Deriv Q
--
-- a second proof of the refutation branch of Theorem 6.1, with no elimination,
-- no greatest fixed point and no round numbering in it: the induction is the
-- reverse traversal of the condensation DAG that the certificate records.
--
-- What is reused, and it is the whole point of the phase.
--
--   stepLemma      -- (Step), Lemma 2.7, unchanged
--   extractR1      -- the sink case, unchanged and used verbatim
--   Refuted        -- the induction hypothesis, unchanged
--   provableEach's -- the three-position argument, minus its middle case
--
-- and what is NOT reused is extractR2, for the reason PHASE11-PLAN.md gives:
-- extractR2 is stated for  gfpW P us A  and uses gfpIn, gfpHolds and gfpClosed,
-- so it is welded to the greatest fixed point.  extractBlock below is its copy
-- with those three facts turned into three hypotheses, which the certificate's
-- block supplies instead.  Nothing in LTL.Extract is touched: C8 compares three
-- procedures and needs all of them.
--
-- The fit with certAll, hypothesis by hypothesis.
--
-- 1. THE SINK CASE IS extractR1 ON THE NOSE.  certAll's sink hypothesis is
--
--        Eq (nullB (outs ws G x)) true
--
--    and at  G = step P  that is  Eq (r1 P ws x) true  DEFINITIONALLY --
--    outs ws (step P) x  and  succs P ws x  are both  filterL (step P x) ws .
--    sinkStep is one line and no coercion appears in it.
--
-- 2. THE BLOCK CASE IS (R2) WITH THE FIXED POINT REPLACED BY THE COMPONENT.
--    certAll's block hypothesis hands over a set C, a proof that it is closed
--    under G-successors inside ws, and a fairness predicate f that C misses
--    everywhere.  With  f = evPred P A ,  Eq (evPred P A y) false  splits into
--
--        Eq (valOf P y (box A)) false     box A pending at y
--        Eq (valOf P y A) true            and unfulfilled at y
--
--    -- the two hypotheses (R2) needs, now at EVERY state of C rather than at
--    one state per round.  That is the improvement PHASE11-PLAN.md predicted
--    from uniformity on a component: extractBlock refutes the whole component
--    in one use of (Ind), where elimRound needs one round per state.
--
-- 3. THE ONE WRINKLE, AND WHY IT IS PAID BY A FILTER.  certAll quantifies its
--    two hypotheses over an arbitrary vertex list ws and knows nothing about
--    Ust P -- it is the graph layer's induction principle and has no business
--    knowing.  extractBlock, on the other hand, needs every member of the block
--    to be a state of Ust P, since chi and the step lemma are stated there.
--    Rather than thread a subset invariant through certAll, the block is
--    intersected with Ust P on the spot:
--
--        D = filterL (\ y -> memB y (Ust P)) C
--
--    and D is still successor-closed, because ustClosed says Ust P is: a
--    successor of a member of D that is a state lands in C by C's closure and
--    in Ust P by ustClosed, hence in D.  The eventuality is still pending and
--    unfulfilled throughout D since D is a sublist of C, and the state being
--    refuted is in D because certAll's own conclusion hands over its
--    Ust-membership.  So certAll is used exactly as it stands, and R carries
--    the Ust-membership as a hypothesis:
--
--        UstRef P z = Mem z (Ust P) -> Deriv (neg (chi P z))
--
--    which is Refuted with the quantifier over ws stripped -- the ONE thing
--    certAll's conclusion has that Refuted's does not.
--
-- The search this consumes is graphGo over the whole of Ust P, not fairGraph
-- from a single vertex: fairGraph's certificate is for  reachSet vs G v , and
-- certAll would then need every state outside that reachable set already
-- refuted, which nothing supplies.  Over Ust P itself the starting hypothesis
-- is  ustRefuted , which is vacuous, and that is why the negative branch needs
-- no seed at all.
--
-- What this does NOT do.  It does not prove that a certificate exists whenever
-- Q is derivable, i.e. that the two branches of sccProof decide validity; that
-- is the dichotomy, and joining it to G38 is G40.  Here the certificate is a
-- hypothesis and the theorem is unconditional on it.

module LTL.SccExtract where

open import LTL.SccLasso public
open import LTL.Extract  public

------------------------------------------------------------------------
-- The property certAll establishes.
--
-- Refuted P us is "every state of Ust P outside us is refutable"; certAll's
-- conclusion is a predicate of a bare vertex, with the "outside us" discharged
-- by the induction.  What is left is the Ust-membership, so that is what R
-- carries.

UstRef : Formula -> Val -> Set
UstRef P z = Mem z (Ust P) -> Deriv (neg (chi P z))

refutedOf : (P : Formula) (ws : List Val)
         -> ((z : Val) -> Eq (memB z ws) false -> UstRef P z) -> Refuted P ws
refutedOf P ws ih u mu e = ih u e mu

------------------------------------------------------------------------
-- The block case: (R2) against a component instead of against gfpW.
--
-- This is extractR2 of LTL.Extract with its three uses of the fixed point --
-- gfpIn, gfpHolds, gfpClosed -- turned into the three hypotheses cUst, cHold,
-- cCl, and with the closure stated in the form the proof actually uses: the
-- successor offered by the step lemma is already known to be a state, and the
-- only question is whether it is still inside ws.  The body is otherwise the
-- note's argument unchanged: (i) B -> A by (L2) and (L5), (ii) B -> nxt B by
-- the step lemma, dropping the successors outside ws by the induction
-- hypothesis and keeping the rest by closure, (iii) B -> box A by (Ind).

extractBlock : (P : Formula) (ws C : List Val) (u : Val)
            -> Mem u (Ust P) -> Refuted P ws
            -> (A : Formula) -> Mem (box A) (sub P)
            -> ((z : Val) -> Mem z C -> Mem z (Ust P))
            -> ((z y : Val) -> Mem z C -> Mem y (St P) -> Eq (memB y ws) true
                  -> Eq (step P z y) true -> Mem y C)
            -> ((z : Val) -> Mem z C -> Eq (valOf P z A) true)
            -> Eq (valOf P u (box A)) false -> Mem u C
            -> Deriv (neg (chi P u))
extractBlock P ws C u mu ih A mbox cUst cCl cHold pend mc = refute chiBox chiNegBox
  where
    lenC : (w : Val) -> Mem w C -> Eq (length w) (length (sub P))
    lenC w m = stLen P (ustSt P (cUst w m))

    -- (i)
    bA : Deriv (imp (beta P C) A)
    bA = betaElim P C eachA
      where
        eachA : (w : Val) -> Mem w C -> Deriv (imp (chi P w) A)
        eachA w m = eqSubst (\ b -> Deriv (imp (chi P w) (lit A b))) (cHold w m)
                            (chiProjVal P w (lenC w m) (sub_box P mbox))

    -- (ii)
    toC : (w : Val) -> Mem w C
       -> Deriv (imp (beta P (succs P (St P) w)) (beta P C))
    toC w m = betaElim P (succs P (St P) w) eachS
      where
        eachS : (w' : Val) -> Mem w' (succs P (St P) w)
             -> Deriv (imp (chi P w') (beta P C))
        eachS w' m' = go (memB w' ws) refl
          where
            pr : Prod (Mem w' (St P)) (Eq (step P w w') true)
            pr = succsMem P (St P) w m'

            go : (b : Bool) -> Eq (memB w' ws) b
              -> Deriv (imp (chi P w') (beta P C))
            go false eb =
              mp negElim (ih w' (ustClosed P (cUst w m) (prodFst pr) (prodSnd pr)) eb)
            go true  eb = betaIntro P C (cCl w w' m (prodFst pr) eb (prodSnd pr))

    bNext : Deriv (imp (beta P C) (nxt (beta P C)))
    bNext = betaElim P C eachN
      where
        eachN : (w : Val) -> Mem w C -> Deriv (imp (chi P w) (nxt (beta P C)))
        eachN w m = impTrans (stepLemma P w (lenC w m)) (nxtMono (toC w m))

    -- (iii)
    chiBox : Deriv (imp (chi P u) (box A))
    chiBox = impTrans (betaIntro P C mc) (impTrans (indRule bNext) (boxMono bA))

    chiNegBox : Deriv (imp (chi P u) (neg (box A)))
    chiNegBox = eqSubst (\ b -> Deriv (imp (chi P u) (lit (box A) b))) pend
                        (chiProjVal P u (stLen P (ustSt P mu)) mbox)

------------------------------------------------------------------------
-- certAll's two hypotheses.

-- The sink.  Eq (nullB (outs ws (step P) x)) true  IS  Eq (r1 P ws x) true .

sinkStep : (P : Formula) (ws : List Val) (x : Val) -> Mem x ws
        -> Eq (nullB (outs ws (step P) x)) true
        -> ((z : Val) -> Eq (memB z ws) false -> UstRef P z)
        -> UstRef P x
sinkStep P ws x mx e1 ih mu = extractR1 P ws x mu (refutedOf P ws ih) e1

-- The block.  The fairness predicate is read back as an eventuality by
-- evPredsInv, its falsity on C is split into the two hypotheses of (R2), and
-- the component is intersected with Ust P.

blockStep : (P : Formula) (ws C : List Val) (f : Val -> Bool) -> Mem f (evPreds P)
         -> ((z : Val) -> Mem z C -> Mem z ws)
         -> ((z y : Val) -> Mem z C -> Mem y ws -> Eq (step P z y) true -> Mem y C)
         -> ((z : Val) -> Mem z C -> Eq (f z) false)
         -> ((z : Val) -> Eq (memB z ws) false -> UstRef P z)
         -> (z : Val) -> Mem z C -> UstRef P z
blockStep P ws C f mf sbC cl mis ih z mz mzU = onA (evPredsInv P mf)
  where
    onA : Sigma Formula
                (\ A -> Prod (Mem A (boxArgs (sub P))) (Eq f (evPred P A)))
       -> Deriv (neg (chi P z))
    onA (sig A (prod mA ef)) =
      extractBlock P ws D z mzU (refutedOf P ws ih) A (boxArgs_mem (sub P) mA)
                   dUst dCl dHold pend mzD
      where
        missA : (y : Val) -> Mem y C -> Eq (evPred P A y) false
        missA y my = eqSubst (\ h -> Eq (h y) false) ef (mis y my)

        -- the component, cut down to the states chi is stated for
        D : List Val
        D = filterL (\ y -> memB y (Ust P)) C

        dC : (y : Val) -> Mem y D -> Mem y C
        dC y m = filter_sub (\ t -> memB t (Ust P)) C m

        dUst : (y : Val) -> Mem y D -> Mem y (Ust P)
        dUst y m = memB_sound y (Ust P) (filter_prop (\ t -> memB t (Ust P)) C m)

        into : (y : Val) -> Mem y C -> Mem y (Ust P) -> Mem y D
        into y my mu =
          filter_true (\ t -> memB t (Ust P)) C my (memB_complete y (Ust P) mu)

        -- still closed: C's closure puts the successor in C, ustClosed puts it
        -- in Ust P, and D is the intersection
        dCl : (y y' : Val) -> Mem y D -> Mem y' (St P) -> Eq (memB y' ws) true
           -> Eq (step P y y') true -> Mem y' D
        dCl y y' my my' ew st =
          into y' (cl y y' (dC y my) (memB_sound y' ws ew) st)
                  (ustClosed P (dUst y my) my' st)

        dHold : (y : Val) -> Mem y D -> Eq (valOf P y A) true
        dHold y my =
          notFalse (valOf P y A)
                   (orFalseR (valOf P y (box A)) (boolNot (valOf P y A))
                             (missA y (dC y my)))

        pend : Eq (valOf P z (box A)) false
        pend = orFalseL (valOf P z (box A)) (boolNot (valOf P z A)) (missA z mz)

        mzD : Mem z D
        mzD = into z mz mzU

------------------------------------------------------------------------
-- G39: a certificate refutes everything it covers.

certRefuted : (P : Formula) {ws : List Val}
           -> Cert (step P) (evPreds P) ws -> Refuted P ws
           -> (z : Val) -> Mem z (Ust P) -> Deriv (neg (chi P z))
certRefuted P {ws} c ih =
  certAll (step P) (evPreds P) (UstRef P) (sinkStep P) (blockStep P) c
          (\ z e mu -> ih z mu e)

-- Over Ust P itself the seed is vacuous: nothing is outside.

ustCertRefuted : (P : Formula) -> Cert (step P) (evPreds P) (Ust P)
              -> (z : Val) -> Mem z (Ust P) -> Deriv (neg (chi P z))
ustCertRefuted P c = certRefuted P c (ustRefuted P)

------------------------------------------------------------------------
-- The search, run on the whole state set.
--
-- graphGo rather than fairGraph: fairGraph is v-centred and certifies only the
-- reachable set of v, while the refutation branch has to account for every
-- state of Ust P at once.  The vertex list is Ust P and the Bar is its own
-- listBar, exactly as fairGraph does for reachSet.

sccGraph : (P : Formula)
        -> Sum (FairIn (Ust P) (step P) (evPreds P))
               (Cert (step P) (evPreds P) (Ust P))
sccGraph P = graphGo (step P) (evPreds P) (Ust P) (memInE (Ust P)) (listBar (Ust P))

------------------------------------------------------------------------
-- The refutation branch of Theorem 6.1, by the SCC route.
--
-- provableEach of LTL.Extract has three cases; this has two.  The state that
-- never joined the search is disposed of by ustSeed exactly as there, and every
-- state that did join is refuted outright -- there is no third case, because
-- there is no surviving set: the certificate covers all of Ust P.  That is the
-- structural difference between the two procedures and it is visible here in
-- the absence of satB.

provableEachSCC : (Q : Formula)
               -> Cert (step (neg Q)) (evPreds (neg Q)) (Ust (neg Q))
               -> (w : Val) -> Mem w (St (neg Q)) -> Deriv (imp (chi (neg Q) w) Q)
provableEachSCC Q c w m = outer (memB w (Ust R)) refl
  where
    R : Formula
    R = neg Q

    fromR : Eq (valOf R w R) false -> Deriv (imp (chi R w) Q)
    fromR ev =
      impTrans (eqSubst (\ d -> Deriv (imp (chi R w) (lit R d))) ev
                        (chiProjVal R w (stLen R m) (sub_self R)))
               dne

    outer : (b : Bool) -> Eq (memB w (Ust R)) b -> Deriv (imp (chi R w) Q)
    outer false ec = fromR (notIn (valOf R w R) refl)
      where
        notIn : (d : Bool) -> Eq (valOf R w R) d -> Eq (valOf R w R) false
        notIn false ed = ed
        notIn true  ed =
          emptyElim (memB_false w (Ust R) ec (ustSeed R m ed))
    outer true  ec = mp negElim (ustCertRefuted R c w (memB_sound w (Ust R) ec))

provableSCC : (Q : Formula)
           -> Cert (step (neg Q)) (evPreds (neg Q)) (Ust (neg Q)) -> Deriv Q
provableSCC Q c =
  mp (betaElim (neg Q) (St (neg Q)) (provableEachSCC Q c)) (stateComplete (neg Q))

------------------------------------------------------------------------
-- The two branches, side by side.
--
-- Not yet a decision: nothing here says the left branch cannot occur when Q is
-- valid, which is the dichotomy and is G40.  What it is, is the negative half
-- of Theorem 6.1 obtained without the elimination.

sccProof : (Q : Formula)
        -> Sum (FairIn (Ust (neg Q)) (step (neg Q)) (evPreds (neg Q))) (Deriv Q)
sccProof Q = sumElim inl (\ c -> inr (provableSCC Q c)) (sccGraph (neg Q))

-- Reading a derivation out, on the strength of the computed boolean: gotLoop
-- says which branch was taken, and refl in the checks below says the search was
-- actually run.

proofFrom : {A : Set} {Q : Formula}
         -> (s : Sum A (Deriv Q)) -> Eq (gotLoop s) false -> Deriv Q
proofFrom (inl a) ()
proofFrom (inr d) e = d

-- and the shape of the certificate, as in cert_P of LTL.Graph: 2 for cBlock,
-- 1 for cSink, 0 for cNil.

sccShape : (Q : Formula) -> List Nat
sccShape Q = sumElim (\ fi -> []) certShape (sccGraph (neg Q))

------------------------------------------------------------------------
-- Checkpoints.
--
-- Ben-Ari's formula and  box p -> box (nxt p) , the two examples LTL.Extract
-- ends with, decided again by the SCC route.  These are the real test: both
-- derivations are produced, so the graph search, certAll, extractR1 and
-- extractBlock all run, and the answers agree with benAriProof and bnbProof.

scc_benAri : Eq (gotLoop (sccProof benAri)) false
scc_benAri = refl

benAriProofSCC : Deriv benAri
benAriProofSCC = proofFrom (sccProof benAri) refl

scc_bnb : Eq (gotLoop (sccProof bnb)) false
scc_bnb = refl

bnbProofSCC : Deriv bnb
bnbProofSCC = proofFrom (sccProof bnb) refl

-- The certificates themselves, read as their removal orders.  For Ben-Ari's
-- formula Ust has one state, it is a sink, and the certificate is  cSink, cNil
-- -- only extractR1 runs, which is what LTL.Extract records of benAriProof.
--
-- For  box p -> box (nxt p)  Ust has two states and the certificate is
-- cSink, cBlock, cNil : one state has no successor inside the set and leaves
-- first, and only then is what remains a component whose eventuality is
-- unfulfillable, refuted by extractBlock in a single use of (Ind).  That is the
-- same order as the elimination's -- G30's note "bnb still exercises (R2), now
-- in the second round rather than the first, because the (R1)-victim has to
-- leave before the eventuality is unfulfillable" -- reached by a different
-- route, and it is why bnb is the example that matters: extractBlock, the copy
-- of (R2), is on the path from here to bnbProofSCC.

shape_benAri : Eq (sccShape benAri) (1 :: 0 :: [])
shape_benAri = refl

shape_bnb : Eq (sccShape bnb) (1 :: 2 :: 0 :: [])
shape_bnb = refl

-- and the positive side, to show the search is not simply always certifying:
-- dia p is satisfiable, so its state set has a fair component.

scc_diaP : Eq (gotLoop (sccGraph diaP)) true
scc_diaP = refl
