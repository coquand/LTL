{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Extract -- G21 of FORMALISATION-PLAN.md, Theorem 4.1 of m4.tex.
--
--   extract : Mem v (removed P) -> Deriv (neg (chi P v))
--
-- The note argues by induction on the round at which v is removed, with the
-- induction hypothesis "every state outside U_k is refutable".  Here that
-- hypothesis is named,
--
--   Refuted P us = every state of St P outside us is refutable,
--
-- and the induction is the obvious one on the fuel of elimIter: Refuted holds
-- of St P for nothing, is carried across one round by roundRefuted, hence holds
-- of Uinf P.  No round numbering appears.
--
-- The two cases of roundRefuted are the note's.  (R1) drops all successors by
-- the hypothesis and closes with (D1) and (Lin).  (R2) builds the loop
-- invariant B = beta_W and refutes the pending eventuality with a single use of
-- (Ind), through indRule; W is the closed set of LTL.Gfp, and step (ii) is
-- exactly its closure property.

module LTL.Extract where

open import LTL.Trace     public
open import LTL.StepLemma public

------------------------------------------------------------------------
-- Every state has the length chi expects

allLen_mem : {n : Nat} {vs : List Val} -> AllLen n vs -> {v : Val}
          -> Mem v vs -> Eq (length v) n
allLen_mem alNil         ()
allLen_mem (alCons e al) memHd     = e
allLen_mem (alCons e al) (memTl m) = allLen_mem al m

stAllLen : (P : Formula) -> AllLen (length (sub P)) (St P)
stAllLen P = allLen_filter (isState P) (allVecs_allLen (length (sub P)))

stLen : (P : Formula) {v : Val} -> Mem v (St P)
     -> Eq (length v) (length (sub P))
stLen P m = allLen_mem (stAllLen P) m

------------------------------------------------------------------------
-- beta_U as a disjunction indexed by states.
--
-- (L5) in the form the theorem uses: introduction at one state, elimination
-- over all of them, and the refutation of a beta all of whose disjuncts are
-- refuted -- which is (L0) when the list is empty, since beta [] is bot and
-- disjElim [] is exFalso.

allIMap : {C : Formula} (f : Val -> Formula) (ws : List Val)
       -> ((w : Val) -> Mem w ws -> Deriv (imp (f w) C)) -> AllI C (map f ws)
allIMap f []        h = aiNil
allIMap f (w :: ws) h = aiCons (h w memHd) (allIMap f ws (\ z m -> h z (memTl m)))

betaElim : (P : Formula) {C : Formula} (ws : List Val)
        -> ((w : Val) -> Mem w ws -> Deriv (imp (chi P w) C))
        -> Deriv (imp (beta P ws) C)
betaElim P ws h = disjElim (map (chi P) ws) (allIMap (chi P) ws h)

betaIntro : (P : Formula) (ws : List Val) {w : Val}
         -> Mem w ws -> Deriv (imp (chi P w) (beta P ws))
betaIntro P ws m = disjIntro (map (chi P) ws) (memMap (chi P) m)

negBeta : (P : Formula) (ws : List Val)
       -> ((w : Val) -> Mem w ws -> Deriv (neg (chi P w)))
       -> Deriv (neg (beta P ws))
negBeta P ws h =
  refute {beta P ws} {top}
         (liftP derivTop)
         (betaElim P ws (\ w m -> mp negElim (h w m)))

------------------------------------------------------------------------
-- The induction hypothesis of the theorem

-- The induction hypothesis ranges over Ust P, the set the search explores, not
-- over St P: a state outside Ust P is never removed and never has to be
-- refuted -- the provable branch disposes of it by (S1) instead.  What makes
-- the change possible is ustClosed, used in both cases below: the step lemma
-- offers ALL state-successors of u, and forward-closure puts each of them back
-- inside Ust P, where the hypothesis applies.

Refuted : Formula -> List Val -> Set
Refuted P us =
  (u : Val) -> Mem u (Ust P) -> Eq (memB u us) false -> Deriv (neg (chi P u))

SubSt : Formula -> List Val -> Set
SubSt P us = (x : Val) -> Mem x us -> Mem x (Ust P)

------------------------------------------------------------------------
-- Case (R1).
--
-- stepLemma gives the successors of u inside St P, while (R1) speaks of U_k;
-- but a successor lying in U_k would be a member of succs P us u, which (R1)
-- says is empty.  So every disjunct of beta_S is refuted by the hypothesis,
-- (D1) puts the refutation under nxt, and (Lin) brings the negation out.

extractR1 : (P : Formula) (us : List Val) (u : Val)
         -> Mem u (Ust P) -> Refuted P us -> Eq (r1 P us u) true
         -> Deriv (neg (chi P u))
extractR1 P us u mu ih e1 =
  refute (stepLemma P u (stLen P (ustSt P mu)))
         (liftP (mp linF (nxtGen (negBeta P (succs P (St P) u) each))))
  where
    outside : (w : Val) -> Mem w (succs P (St P) u) -> Eq (memB w us) false
    outside w m = go (memB w us) refl
      where
        go : (b : Bool) -> Eq (memB w us) b -> Eq (memB w us) false
        go false eb = eb
        go true  eb =
          emptyElim (nullB_mem (succs P us u) e1
                      (succsIn P us u (memB_sound w us eb)
                               (prodSnd (succsMem P (St P) u m))))

    each : (w : Val) -> Mem w (succs P (St P) u) -> Deriv (neg (chi P w))
    each w m = ih w (ustClosed P mu (prodFst (succsMem P (St P) u m))
                               (prodSnd (succsMem P (St P) u m)))
                 (outside w m)

------------------------------------------------------------------------
-- Case (R2).
--
-- B := beta_W is the loop invariant, W the closed set of LTL.Gfp.  The three
-- steps of the note, in order: (i) B -> A by (L2) and (L5), since A holds
-- throughout W; (ii) B -> nxt B by the step lemma, dropping the successors
-- that left U_k by the induction hypothesis and keeping the rest by closure of
-- W; (iii) B -> box A by (Ind) through indRule and (D3) through boxMono.
-- Then u lies in W, so chi_u -> box A, while the eventuality is pending at u,
-- so chi_u -> neg (box A).

extractR2 : (P : Formula) (us : List Val) (u : Val)
         -> Mem u (Ust P) -> SubSt P us -> Refuted P us
         -> (A : Formula) -> Mem (box A) (sub P)
         -> Eq (valOf P u (box A)) false -> Mem u (gfpW P us A)
         -> Deriv (neg (chi P u))
extractR2 P us u mu sb ih A mbox pend mgfp = refute chiBox chiNegBox
  where
    W : List Val
    W = gfpW P us A

    lenW : (w : Val) -> Mem w W -> Eq (length w) (length (sub P))
    lenW w m = stLen P (ustSt P (sb w (gfpIn P us A m)))

    -- (i)
    bA : Deriv (imp (beta P W) A)
    bA = betaElim P W eachA
      where
        eachA : (w : Val) -> Mem w W -> Deriv (imp (chi P w) A)
        eachA w m = eqSubst (\ b -> Deriv (imp (chi P w) (lit A b)))
                            (gfpHolds P us A m)
                            (chiProjVal P w (lenW w m) (sub_box P mbox))

    -- (ii)
    toW : (w : Val) -> Mem w W
       -> Deriv (imp (beta P (succs P (St P) w)) (beta P W))
    toW w m = betaElim P (succs P (St P) w) eachS
      where
        eachS : (w' : Val) -> Mem w' (succs P (St P) w)
             -> Deriv (imp (chi P w') (beta P W))
        eachS w' m' = go (memB w' us) refl
          where
            pr : Prod (Mem w' (St P)) (Eq (step P w w') true)
            pr = succsMem P (St P) w m'

            go : (b : Bool) -> Eq (memB w' us) b
              -> Deriv (imp (chi P w') (beta P W))
            go false eb =
              mp negElim (ih w' (ustClosed P (sb w (gfpIn P us A m))
                                           (prodFst pr) (prodSnd pr)) eb)
            go true  eb = betaIntro P W (gfpClosed P us A w w' m
                                                   (memB_sound w' us eb)
                                                   (prodSnd pr))

    bNext : Deriv (imp (beta P W) (nxt (beta P W)))
    bNext = betaElim P W eachN
      where
        eachN : (w : Val) -> Mem w W -> Deriv (imp (chi P w) (nxt (beta P W)))
        eachN w m = impTrans (stepLemma P w (lenW w m)) (nxtMono (toW w m))

    -- (iii)
    chiBox : Deriv (imp (chi P u) (box A))
    chiBox = impTrans (betaIntro P W mgfp)
                      (impTrans (indRule bNext) (boxMono bA))

    chiNegBox : Deriv (imp (chi P u) (neg (box A)))
    chiNegBox = eqSubst (\ b -> Deriv (imp (chi P u) (lit (box A) b))) pend
                        (chiProjVal P u (stLen P (ustSt P mu)) mbox)

------------------------------------------------------------------------
-- One round of the elimination preserves the hypothesis

roundRefuted : (P : Formula) (us : List Val)
            -> SubSt P us -> Refuted P us -> Refuted P (elimRound P us)
roundRefuted P us sb ih u mu e = onMem (memB u us) refl
  where
    gs : List Ev
    gs = evList P us

    onMem : (b : Bool) -> Eq (memB u us) b -> Deriv (neg (chi P u))
    onMem false eb = ih u mu eb
    onMem true  eb = byReason (dropped P us u (kf (keep P us gs u) refl))
      where
        mus : Mem u us
        mus = memB_sound u us eb

        kf : (b : Bool) -> Eq (keep P us gs u) b -> Eq (keep P us gs u) false
        kf false ek = ek
        kf true  ek = emptyElim (memB_false u (elimRound P us) e
                                            (filter_true (keep P us gs) us mus ek))

        byReason : Reason P us u -> Deriv (neg (chi P u))
        byReason (byR1 e1)                = extractR1 P us u mu ih e1
        byReason (byR2 A mbox pend mgfp)  =
          extractR2 P us u mu sb ih A mbox pend mgfp

------------------------------------------------------------------------
-- Theorem 4.1

elimRoundSub : (P : Formula) (us : List Val)
            -> SubSt P us -> SubSt P (elimRound P us)
elimRoundSub P us sb x m = sb x (filter_sub (keep P us (evList P us)) us m)

ustRefuted : (P : Formula) -> Refuted P (Ust P)
ustRefuted P u mu e = emptyElim (memB_false u (Ust P) e mu)

-- The induction that used to run along the fuel of elimIter now runs along the
-- Bar that elimGo runs on, and it is the same induction: the hypothesis is
-- carried across one round by roundRefuted in the branch where a round removes
-- something, and returned unchanged in the branch where none does.

goRefuted   : (P : Formula) {E : Val -> Bool} (us : List Val)
           -> (sb : InE E us) (bar : IFin E)
           -> SubSt P us -> Refuted P us -> Refuted P (elimGo P us sb bar)
findRefuted : (P : Formula) {E : Val -> Bool} (us : List Val)
           -> (sb : InE E us) (bar : IFin E)
           -> (fr : FindResult (keep P us (evList P us)) us)
           -> SubSt P us -> Refuted P us -> Refuted P (elimFind P us sb bar fr)

goRefuted P us sb bar =
  findRefuted P us sb bar (findFalse (keep P us (evList P us)) us)

findRefuted P us sb bar      (allT f)       ss r = r
findRefuted P us sb (cBar h) (found x mx q) ss r =
  goRefuted P (elimRound P us)
            (dropInE (keep P us (evList P us)) us sb x q) (h x (sb x mx))
            (elimRoundSub P us ss) (roundRefuted P us ss r)

uinfRefuted : (P : Formula) -> Refuted P (Uinf P)
uinfRefuted P =
  goRefuted P (Ust P) (ustInE P) (ustBar P) (\ x m -> m) (ustRefuted P)

extract : (P : Formula) {v : Val} -> Mem v (removed P) -> Deriv (neg (chi P v))
extract P {v} m =
  uinfRefuted P v
              (filter_sub (\ z -> boolNot (memB z (Uinf P))) (Ust P) m)
              (notTrue (memB v (Uinf P))
                       (filter_prop (\ z -> boolNot (memB z (Uinf P))) (Ust P) m))

------------------------------------------------------------------------
-- The provable branch of Theorem 6.1.
--
-- Every state of St (neg Q) is now in one of three positions, and the first is
-- what G30 added.  It never enters the search at all: a state outside Ust R
-- cannot contain R, by the contrapositive of ustSeed, so chi_w carries
-- neg R = neg (neg Q) outright.  Of the states inside Ust R, the removed ones
-- are refuted by extraction and the survivors do not contain R either, because
-- satB says so.  All three end at the same place, and state completeness --
-- which quantifies over ALL of St R, and is why St R stays what it is -- gives
-- Q.  This is one of the two branches of G28; the other needs the lasso.

-- The three cases are a top-level function rather than a where-block of
-- provable, so that the short certificate of Phase 9 can reuse them: what
-- provablePC (LTL.ShortPC) changes is the OTHER half of the modus ponens, the
-- state completeness, and nothing here.

provableEach : (Q : Formula) -> Eq (satB (neg Q)) false
            -> (w : Val) -> Mem w (St (neg Q))
            -> Deriv (imp (chi (neg Q) w) Q)
provableEach Q e w m = outer (memB w (Ust R)) refl
  where
    R : Formula
    R = neg Q

    -- w does not contain R, however that was found out
    fromR : Eq (valOf R w R) false -> Deriv (imp (chi R w) Q)
    fromR ev =
      impTrans (eqSubst (\ c -> Deriv (imp (chi R w) (lit R c))) ev
                        (chiProjVal R w (stLen R m) (sub_self R)))
               dne

    -- w never joined the search, so by ustSeed it does not contain R
    outer : (c : Bool) -> Eq (memB w (Ust R)) c -> Deriv (imp (chi R w) Q)
    outer false ec = fromR (notIn (valOf R w R) refl)
      where
        notIn : (d : Bool) -> Eq (valOf R w R) d -> Eq (valOf R w R) false
        notIn false ed = ed
        notIn true  ed =
          emptyElim (memB_false w (Ust R) ec (ustSeed R m ed))
    outer true  ec = go (memB w (Uinf R)) refl
      where
        mu : Mem w (Ust R)
        mu = memB_sound w (Ust R) ec

        -- w survived, so satB says it does not contain R either
        go : (b : Bool) -> Eq (memB w (Uinf R)) b -> Deriv (imp (chi R w) Q)
        go true  eb =
          fromR (anyL_false (\ z -> valOf R z R) (Uinf R) e
                            (memB_sound w (Uinf R) eb))
        -- w was removed, so chi_w is refutable
        go false eb =
          mp negElim
             (extract R (filter_true (\ z -> boolNot (memB z (Uinf R)))
                                     (Ust R) mu (eqCong boolNot eb)))

provable : (Q : Formula) -> Eq (satB (neg Q)) false -> Deriv Q
provable Q e =
  mp (betaElim (neg Q) (St (neg Q)) (provableEach Q e)) (stateComplete (neg Q))

------------------------------------------------------------------------
-- Checkpoint.
--
-- Ben-Ari's formula, decided.  The procedure removes both states containing
-- neg benAri, so provable returns a derivation of  box p -> nxt (box p)  in the
-- system L.  This is the first half of C4, reached without Phase 6: the
-- refutation branch of Theorem 6.1 is complete on its own.

benAriProof : Deriv benAri
benAriProof = provable benAri satB_negBenAri

-- The same for  box p -> box (nxt p) .  This is the example that matters as a
-- test: by trace_negBnb of LTL.Trace its refutation passes through case (R2),
-- so extractR2 -- the loop invariant, (Ind) and all -- is on the path from
-- satB_negBnb to this derivation, where for benAri only extractR1 is.

bnbProof : Deriv bnb
bnbProof = provable bnb satB_negBnb
