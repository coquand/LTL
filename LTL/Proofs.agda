{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Proofs -- printing the derivation decide returns, and what it costs.
--
-- On the inl branch decide returns a term of Deriv Q, and a derivation is a
-- finite tree, so it can simply be printed.  showD does that, to a given depth, carrying the
-- formula proved at each node; shapeD does it without the formulas, which is
-- what one wants as soon as the tree is more than a few nodes deep.
--
-- The depth argument is not a convenience.  The middle sections measure the
-- certificates, and the answer is that they are enormous: decide proves
-- p -> p with 82357 constructors where impRefl proves it with 5.  The reason
-- is structural and is worth stating, because it is the price of the design
-- that made Phase 8 possible.
--
-- The last section, C6, is the answer Phase 9 gives and what Phase 10 does to
-- it.  For  p -> p :  82357 constructors, then 139 once Lemma 2.6 is one (PC)
-- line, then 7 once the branches are (G34), then ONE once the disjunction they
-- were branches of goes with them.  Every number is checked here, against the
-- same formula, because every proof is still in the development -- see
-- LTL.CompletePC and LTL.ShortPC.  Nothing between here and there changes.
--
-- The file takes about 66 s, of which 9 is one line: c6_k5_side runs the side
-- condition of the axK5fwd certificate, which is the check the long certificate
-- could not make.  It is a benchmark, and the 5 s rule of section 4a does not
-- apply to it.

module LTL.Proofs where

open import LTL.Examples public
open import LTL.ShortPC  public

------------------------------------------------------------------------
-- The ten constructors, named

data Rule : Set where
  rP1 rP2 rP3 rKbox rKnxt rExp rInd rLin rPc rMp rGen : Rule
  rMore : Rule                       -- the depth bound was reached here

-- dnil and rnil mean "no derivation": they are what the printers return when
-- decide took the inr branch.  Having a second constructor is also what makes
-- a tree printable at all -- against a one-constructor type Agda reports the
-- first differing node, against nil it reports the whole tree.

data DTree : Set where
  dnil : DTree
  node : Rule -> Formula -> List DTree -> DTree

data RTree : Set where
  rnil  : RTree
  rnode : Rule -> List RTree -> RTree

showD : {A : Formula} -> Nat -> Deriv A -> DTree
showD {A} zero    d        = node rMore A []
showD {A} (suc n) p1       = node rP1   A []
showD {A} (suc n) p2       = node rP2   A []
showD {A} (suc n) p3       = node rP3   A []
showD {A} (suc n) kbox     = node rKbox A []
showD {A} (suc n) knxt     = node rKnxt A []
showD {A} (suc n) exp      = node rExp  A []
showD {A} (suc n) ind      = node rInd  A []
showD {A} (suc n) lin      = node rLin  A []
showD {A} (suc n) (pc e)   = node rPc   A []
showD {A} (suc n) (mp d e) = node rMp   A (showD n d :: showD n e :: [])
showD {A} (suc n) (gen d)  = node rGen  A (showD n d :: [])

shapeD : {A : Formula} -> Nat -> Deriv A -> RTree
shapeD zero    d        = rnode rMore []
shapeD (suc n) p1       = rnode rP1   []
shapeD (suc n) p2       = rnode rP2   []
shapeD (suc n) p3       = rnode rP3   []
shapeD (suc n) kbox     = rnode rKbox []
shapeD (suc n) knxt     = rnode rKnxt []
shapeD (suc n) exp      = rnode rExp  []
shapeD (suc n) ind      = rnode rInd  []
shapeD (suc n) lin      = rnode rLin  []
shapeD (suc n) (pc e)   = rnode rPc   []
shapeD (suc n) (mp d e) = rnode rMp   (shapeD n d :: shapeD n e :: [])
shapeD (suc n) (gen d)  = rnode rGen  (shapeD n d :: [])

-- and the same for whatever decide returns

shapeOfProof : (Q : Formula) -> Nat -> RTree
shapeOfProof Q n = go (decide Q)
  where
    go : Sum (Deriv Q) (LassoCountermodel Q) -> RTree
    go (inl d) = shapeD n d
    go (inr c) = rnil

------------------------------------------------------------------------
-- Two derivations of the note's own, printed in full.
--
-- (L1), the identity.  Combinatorially it is SKK: (P2) applied to (P1) twice.
-- Five constructors, and with the formula at each node this is the whole proof
-- as one would write it on paper.

taut : Formula
taut = imp pv pv

impRefl_full : Eq (showD 9 (impRefl {pv}))
                  (node rMp taut
                    (node rMp (imp (imp pv taut) taut)
                      (node rP2 (imp (imp pv (imp taut pv))
                                     (imp (imp pv taut) taut)) []
                       :: node rP1 (imp pv (imp taut pv)) []
                       :: [])
                     :: node rP1 (imp pv taut) []
                     :: []))
impRefl_full = refl

-- Double negation elimination.  Checkpoint C2 of FORMALISATION-PLAN.md calls it
-- "the one derivation that took thought": under the antecedent neg (neg A) one
-- has neg A -> neg top by negElim, hence top -> A by (P3), and top is
-- available.  Twenty-three constructors, and the shape shows the argument --
-- the right branch is  mp p1 ident , which is  liftP derivTop , and ident is
-- the identity above, since top IS  p -> p .

ident : RTree
ident = rnode rMp (rnode rMp (rnode rP2 [] :: rnode rP1 [] :: [])
                   :: rnode rP1 [] :: [])

negElimTree : RTree
negElimTree = rnode rMp (rnode rP2 []
                         :: rnode rMp (rnode rP1 [] :: rnode rP3 [] :: [])
                         :: [])

dne_full : Eq (shapeD 20 (dne {pv}))
              (rnode rMp
                (rnode rMp (rnode rP2 []
                            :: rnode rMp (negElimTree
                                          :: rnode rMp (negElimTree
                                                        :: rnode rP1 [] :: [])
                                          :: [])
                            :: [])
                 :: rnode rMp (rnode rP1 [] :: ident :: [])
                 :: []))
dne_full = refl

-- The sizes of a few more, for scale.  Every one is a theorem of L written by
-- hand in LTL.Prop and LTL.Temporal, and every one is small.

hand_sizes : Eq (derivSize (impRefl {pv})   :: derivSize (dne {pv})
              :: derivSize (linF {pv})      :: derivSize (boxElim {pv})
              :: derivSize (boxNxtBox {pv}) :: derivSize (expConv {pv}) :: [])
                (5 :: 23 :: 41 :: 45 :: 77 :: 931 :: [])
hand_sizes = refl

------------------------------------------------------------------------
-- The same theorem, as decide proves it.
--
-- p -> p is the smallest thing decide can be asked: Sub of its negation has
-- length 4, so sixteen valuations.  The certificate has 82357 constructors --
-- 41178 modus ponens steps, no generalisation and no (Ind) -- against the five
-- of impRefl just above, for literally the same formula.

taut_count : Eq (countOf taut) (prod 82357 (prod 41178 (prod 0 0)))
taut_count = refl

-- Its top four levels are modus ponens throughout, with a single (P2) visible:
-- provable Q e is  mp (betaElim ...) (stateComplete ...) , and both halves are
-- chains of modus ponens, the propositional layer being (P1)-(P3) and mp and
-- nothing else (Remark 6.4 of m4.tex).

mm : RTree
mm = rnode rMp (rnode rMore [] :: rnode rMore [] :: [])

mm2 : RTree
mm2 = rnode rMp (mm :: mm :: [])

taut_top : Eq (shapeOfProof taut 4)
              (rnode rMp
                (rnode rMp (rnode rMp (rnode rP2 [] :: mm :: []) :: mm2 :: [])
                 :: rnode rMp (mm2 :: mm2 :: []) :: []))
taut_top = refl

------------------------------------------------------------------------
-- Where the size comes from, and why it is not an accident.
--
--   axT = box p -> p ,  Sub of its negation has length 5, thirty-two
--   valuations.  The certificate has 298321 constructors, of which 296839 --
--   99.5 % -- are stateComplete alone.
--
-- stateComplete P : Deriv (beta P (St P)) is Lemma 2.6, proved by splitting the
-- disjunction over ALL 2^|Sub P| valuations with (L6) and then dropping the
-- non-states.  So the certificate is exponential in |Sub Q|, and inherently so:
-- beta_{St P} being a theorem IS the statement that the state set is complete,
-- and every branch of Theorem 4.1 passes through it.
--
-- This is exactly the object G30 separated out and left alone.  Section 6 of
-- FORMALISATION-PLAN.md says to keep beta (St P) in derivation terms, "where it
-- is typechecked and never normalised", and that split is what made checkpoint
-- C5 possible: deciding  box (p or q) -> box p or box q  takes 0.9 s over a
-- demand-driven set of 8 states, while writing out the derivation it returns
-- would mean normalising a disjunction over 2^22 valuations.  The DECISION is
-- cheap and the CERTIFICATE is not.
--
-- Measured, for the record: axX = box (box p) -> box p, with |Sub| = 7, did not
-- finish in 280 s.  Nothing above |Sub| = 5 is printable, and the counts below
-- are the largest that are.
--
-- Two things before reading this as a defect.  Nothing but this file ever
-- normalises a certificate: decide's own answer, the C1-C5 checkpoints and
-- LTL.Examples all evaluate booleans and lassos, never a Deriv.  And the
-- redundancy is of a particular kind -- half the nodes are modus ponens, so it
-- is the propositional bookkeeping of (L2)-(L6) over the valuations, not the
-- temporal argument, which is what the two zeros record.

axT_count : Eq (countOf axT) (prod 298321 (prod 149160 (prod 0 0)))
axT_count = refl

axT_stateComplete : Eq (derivSize (stateComplete (neg axT))) 296839
axT_stateComplete = refl

-- and the two facts behind the zeros: no state of Sub (neg axT) contains
-- neg axT at all -- (S2) forbids box p together with neg p -- so the
-- demand-driven set is EMPTY, the elimination never runs, and every state is
-- disposed of by the third case of provable, the one G30 added.

axT_states : Eq (length (St (neg axT))) 3
axT_states = refl

axT_search : Eq (length (Ust (neg axT))) 0
axT_search = refl

------------------------------------------------------------------------
-- Can it be compressed?  Where the 82357 actually go.
--
-- The certificate of p -> p splits into three parts, and they are not of
-- comparable size:
--
--    allComplete (sub R)     19263    23 %   the 2^4 = 16 -fold case split
--    disjFilter ...          62099    75 %   refuting the non-states, one by one
--    betaElim R (St R) each    993     1 %   the argument about Q itself
--
-- So ninety-seven per cent of the proof enumerates valuations and then throws
-- most of them away.  Only the last one per cent is about the formula.

taut_parts : Eq (length (sub (neg taut))
              :: derivSize (allComplete (sub (neg taut)))
              :: derivSize (stateComplete (neg taut))
              :: derivSize (provable taut refl) :: [])
                (4 :: 19263 :: 81363 :: 82357 :: [])
taut_parts = refl

-- The case split alone, as the number of formulas split on grows.  Each extra
-- formula doubles it, at about 620-650 constructors per valuation: this is
-- Theta(2^n), and n is |Sub P|, not the number of variables.

split_growth : Eq (derivSize (allComplete [])
               :: derivSize (allComplete (pv :: []))
               :: derivSize (allComplete (pv :: qv :: []))
               :: derivSize (allComplete (pv :: qv :: var 2 :: []))
               :: derivSize (allComplete (pv :: qv :: var 2 :: var 3 :: [])) :: [])
                  (21 :: 1261 :: 3747 :: 8797 :: 19263 :: [])
split_growth = refl

------------------------------------------------------------------------
-- Compression 1: sharing.  It buys almost nothing, and that is worth knowing.
--
-- derivSize counts a TREE.  A Hilbert derivation is really a numbered LIST of
-- lines, so the honest measure is the number of distinct conclusions -- a
-- formula proved twice needs one line, not two.  linesD computes that.
--
-- Measured, the two agree on the small derivations and differ by 28 % on the
-- largest hand-written one.  The reason is that the repeated sub-proofs are
-- repeated at DIFFERENT formula instances: impTrans and weaken are used
-- everywhere, but never twice with the same conclusion.  Sharing is not where
-- the compression is.

linesD : {A : Formula} -> Deriv A -> List Formula -> List Formula
linesD {A} p1       acc = insF A acc
linesD {A} p2       acc = insF A acc
linesD {A} p3       acc = insF A acc
linesD {A} kbox     acc = insF A acc
linesD {A} knxt     acc = insF A acc
linesD {A} exp      acc = insF A acc
linesD {A} ind      acc = insF A acc
linesD {A} lin      acc = insF A acc
linesD {A} (pc e)   acc = insF A acc
linesD {A} (mp d e) acc = insF A (linesD d (linesD e acc))
linesD {A} (gen d)  acc = insF A (linesD d acc)

derivLines : {A : Formula} -> Deriv A -> Nat
derivLines d = length (linesD d [])

sharing : Eq (derivLines (impRefl {pv}) :: derivLines (dne {pv})
           :: derivLines (boxElim {pv}) :: derivLines (expConv {pv}) :: [])
             (5 :: 23 :: 45 :: 667 :: [])
sharing = refl

------------------------------------------------------------------------
-- Compression 2: do not enumerate.  This is where it is.
--
-- allComplete splits on every member of Sub P.  But (S1) DETERMINES the bit at
-- neg A from the bit at A, and the bit at imp A B from those at A and B, and
-- coherence makes the bit a function of the formula rather than of the
-- position.  So the case distinction only has to be made at the ATOMS -- the
-- var, nxt and box entries, deduplicated -- and the compound literals of chi
-- should be DERIVED in each case instead of split on.
--
-- That is exactly the move G30 made on the computational side, where mkV builds
-- a state from an assignment to the atoms and cands replaced 2^|Sub| by
-- 2^|atoms|.  Applied to Lemma 2.6 it would compress the certificate by the
-- same factor, and it would empty disjFilter as well: valuations built from
-- atoms satisfy (S1) and coherence by construction, so the only clause left to
-- refute is (S2), once per atom rather than once per valuation.  That is the
-- 75 % and the 23 % together.
--
-- The factor, on the three formulas of this file:
--
--    p -> p             |Sub| 4,  atoms 1     16 cases  ->      2
--    box p -> p         |Sub| 5,  atoms 2     32 cases  ->      4
--    the C5 formula     |Sub| 22, atoms 8   4194304     ->    256
--
-- so between 8 and 16384 times smaller, and it grows with the propositional
-- structure of the formula, which is the part that is free.
--
-- It is not a small change: stateComplete, nonState and disjFilter are Lemma
-- 2.6 and Lemma 2.5, and beta (St P) would have to become beta over the
-- generated list, with stcSt and stStc of LTL.Closure lifted from membership to
-- derivability.  Recorded here rather than done.

atom_factor : Eq (length (atoms (sub (neg taut)))
               :: length (atoms (sub (neg axT)))
               :: length (atoms (sub (neg axK5fwd))) :: [])
                 (1 :: 2 :: 8 :: [])
atom_factor = refl

------------------------------------------------------------------------
-- (PC) at work, and where it stops.
--
-- The new constructor takes  Eq (isTaut A) true , and isTaut evaluates the
-- skeleton of A over its atoms.  So pc fires on a CONCRETE formula by refl, and
-- on a SCHEMATIC one only through a proof -- which is the price of dropping the
-- substitution relation.  Ben-Ari's Axiom 0 applies to  A -> A  for schematic A
-- because it is a substitution instance of  p -> p ; here one has to say why.
--
-- Saying why is cheap, and it is a BOOLEAN argument rather than a derivation.
-- For A -> A: whatever the skeleton makes of A, boolImp x x is true.  Two lines,
-- and the derivation drops from five constructors to one.

tautSelf : (A : Formula) -> Eq (isTaut (imp A A)) true
tautSelf A =
  allB_intro (\ a -> valFrom (atomsOf (imp A A)) a (imp A A))
             (allVecs (length (atomsOf (imp A A))))
             (\ {a} m -> tid (valFrom (atomsOf (imp A A)) a A))

impReflPc : (A : Formula) -> Deriv (imp A A)
impReflPc A = pc (tautSelf A)

-- and the same for double negation elimination, twenty-three down to one

tdne : (x : Bool) -> Eq (boolImp (boolNot (boolNot x)) x) true
tdne true  = refl
tdne false = refl

tautDne : (A : Formula) -> Eq (isTaut (imp (neg (neg A)) A)) true
tautDne A =
  allB_intro (\ a -> valFrom (atomsOf (imp (neg (neg A)) A)) a (imp (neg (neg A)) A))
             (allVecs (length (atomsOf (imp (neg (neg A)) A))))
             (\ {a} m -> tdne (valFrom (atomsOf (imp (neg (neg A)) A)) a A))

dnePc : (A : Formula) -> Deriv (imp (neg (neg A)) A)
dnePc A = pc (tautDne A)

pc_sizes : Eq (derivSize (impReflPc pv) :: derivSize (dnePc pv)
            :: derivSize (impRefl {pv}) :: derivSize (dne {pv}) :: [])
              (1 :: 1 :: 5 :: 23 :: [])
pc_sizes = refl

-- On a concrete formula it is refl, and the whole proof is one node.

taut_pc : Eq (showD 3 (pc {taut} refl)) (node rPc taut [])
taut_pc = refl

------------------------------------------------------------------------
-- The boundary, checked.
--
-- (PC) is exactly the propositional part.  (Lin) -- nxt (neg A) -> neg (nxt A),
-- which is half of Ben-Ari's Axiom 5 -- is NOT a skeleton tautology: nxt (neg p)
-- and nxt p are two unrelated atoms, so the skeleton reads it as  q -> neg r .
-- The same for (T), box p -> p, where box p is an atom independent of p.  Both
-- have to stay axioms, which is why Ben-Ari's list has five temporal axioms
-- beside PC and ours has seven beside (P1)-(P3).

lin_not_taut : Eq (isTaut (imp (nxt (neg pv)) (neg (nxt pv)))) false
lin_not_taut = refl

boxElim_not_taut : Eq (isTaut (imp (box pv) pv)) false
boxElim_not_taut = refl

-- but the propositional consequences of a temporal axiom are (PC) again:
-- p or neg p, and  (box p -> p) -> (neg p -> neg (box p)) , are both skeleton
-- tautologies, the second because box p is simply an atom.

lem_taut : Eq (isTaut (dis pv (neg pv))) true
lem_taut = refl

contra_taut : Eq (isTaut (imp (imp (box pv) pv) (imp (neg pv) (neg (box pv))))) true
contra_taut = refl

------------------------------------------------------------------------
-- Checkpoint C6: the two certificates, side by side.
--
-- Everything above this line is the ten-constructor system, and none of it
-- changes: decide, allComplete and stateComplete are the terms they always
-- were, and 82357 is still 82357.  Phase 9 puts a SECOND proof of Lemma 2.6
-- beside the first (stateCompletePC, LTL.CompletePC) and a second decision
-- procedure beside decide (decidePC, LTL.ShortPC), and adds nothing to the
-- path from decide to its answer.  That is what makes the comparison below a
-- comparison rather than a replacement -- both proofs are in the development,
-- and Lemma 2.5, which only the old one runs on, is a theorem of m4.tex in its
-- own right.
--
-- The case split first, which is G31.  allComplete (sub (neg taut)) is the
-- 2^4-fold disjunction of section 4g, 19263 constructors of (L6) and modus ponens;
-- allCompletePC is the same formula as a single (PC) line, its side condition
-- proved once and for all by tautAll -- a plain induction on the list, since
-- the witness disjunct is the truth-table row itself.

c6_split : Eq (derivSize (allComplete   (sub (neg taut)))
            :: derivSize (allCompletePC (sub (neg taut))) :: [])
              (19263 :: 1 :: [])
c6_split = refl

-- Then Lemma 2.6, which is G32.  For p -> p there is no box-subformula at all,
-- so the (S2) chain is empty and state completeness is ONE node against 81363.
-- For box p -> p there is one box-subformula, and one instance of (T) is 45
-- constructors, so 47 against 296839 -- the 99.5 % of the axT certificate that
-- section 4g measured, gone in a factor of six thousand.
--
-- The count is exact and it is  1 + 46 |boxArgs (sub P)| : one modus ponens and
-- one boxElim per eventuality, on top of the single (PC) node.  Nothing in it
-- depends on |Sub P|, which is the whole point.

c6_lemma : Eq (derivSize (stateComplete   (neg taut))
            :: derivSize (stateCompletePC (neg taut))
            :: derivSize (stateComplete   (neg axT))
            :: derivSize (stateCompletePC (neg axT)) :: [])
              (81363 :: 1 :: 296839 :: 47 :: [])
c6_lemma = refl

-- and hence the certificates themselves, which is C6 proper: what decide
-- returns for p -> p against what decidePC returns for it.  Same formula, same
-- branch, same countermodel machinery behind both.

c6 : Eq (countOf taut :: countOfPC taut :: [])
        (prod 82357 (prod 41178 (prod 0 0))
      :: prod     1 (prod     0 (prod 0 0)) :: [])
c6 = refl

-- The second (PC) node, and where the rest of the certificate went.
--
-- With Lemma 2.6 at one node the dominant cost was (L5): disjElim proves
-- (C1 or ... or Cn) -> C from the n implications Ci -> C, and dis A B being
-- neg A -> B, it contraposes and double-negates at every cons -- measured, 426
-- constructors PER DISJUNCT.  That is 859 of the 993 below, and it grows with
-- |St P|, so it was the whole certificate as soon as Lemma 2.6 stopped being.
--
-- It is propositional, so (PC) takes it whole: tautDisjElim says the displayed
-- implication is a tautology of its own skeleton, and the n branches are
-- discharged by n modus ponens.  betaElimPC is 1 + n nodes of glue against
-- betaElim's 17 + 426 n, and the certificate is now linear in |St P| with a
-- constant of one.

c6_disjElim : Eq (derivSize (betaElim   (neg taut) (St (neg taut))
                                        (provableEach taut refl))
               :: derivSize (betaElimPC (neg taut) (St (neg taut))
                                        (provableEach taut refl)) :: [])
                 (993 :: 137 :: [])
c6_disjElim = refl

-- What was left after that is the branches themselves: 67 constructors per
-- state, and they are the only part of the certificate that is about Q rather
-- than about the logic.  Each is an easy case of provableEach -- project the
-- conjunct neg neg Q out of chi_w by (L2), 39, then double negation, 23, then
-- (L1), 5.

c6_branch : Eq (derivSize (conjProj (litList (sub (neg taut))
                                             (false :: true :: true :: true :: []))
                                    memHd)
             :: derivSize (dne {neg (neg taut)}) :: []) (39 :: 23 :: [])
c6_branch = refl

-- G34 of PHASE10-PLAN.md removes those too, and by the same observation a
-- third time: chi_w -> Q is a TAUTOLOGY OF ITS OWN SKELETON as soon as the bit
-- of w at neg Q is false, since chi_w then carries the conjunct neg (neg Q)
-- and a conjunction implies its conjuncts.  So provableEachPC (LTL.ShortPC)
-- makes each easy branch one pc node, 67 against 1, and the certificate is
--
--     1 + 2 |St P| + 46 |boxArgs (sub P)| + 2
--
-- exactly: one pc node and one modus ponens per state, 46 per eventuality for
-- Lemma 2.6's chain of (T), one pc node and one modus ponens for (L5).  That is
-- provableStPC (LTL.ShortPC), 7, 55 and 149 for the three formulas below.
--
-- The one case that does NOT collapse is the third, where the state was
-- removed by the elimination: that is extract, Theorem 4.1, and it is not a
-- tautology -- if it were, the temporal argument would be unnecessary.
--
-- And that observation is the whole of the next step.  If two of the three
-- cases are DECIDED rather than derived, they need not be cases at all -- they
-- can be absorbed into the decision -- and then the disjunction they were
-- branches of is not needed either.  provablePC states the propositional part
-- as the single implication
--
--     (S2 chain)  ->  neg chi_{w_1} -> ... -> neg chi_{w_k}  ->  Q
--
-- over the REMOVED states alone, which is a tautology of its own skeleton by
-- betaSkel's argument contraposed, and discharges each premise with extract.
-- So beta, (L5) and every branch except the removed ones disappear together,
-- and the count is
--
--     1  +  46 |boxArgs (sub P)|  +  sum over removed w of (1 + |extract w|)
--
-- with NOTHING indexed by |St P|.  All three formulas below have empty Ust, so
-- for them it is  1 + 46 |boxArgs| : 1, 47 and 139.  The proof of p -> p is one
-- (PC) line, which is what it should always have been.

tautW : Val
tautW = false :: true :: true :: true :: []

c6_branchPC : Eq (derivSize (provableEach   taut refl tautW
                                            (memB_sound tautW (St (neg taut)) refl))
               :: derivSize (provableEachPC taut refl tautW
                                            (memB_sound tautW (St (neg taut)) refl))
               :: []) (67 :: 1 :: [])
c6_branchPC = refl

-- The progression, on one line: Phase 9's certificate is 139, G34's branches
-- take it to 7, and dropping the disjunction takes it to 1.

c6_steps : Eq (derivSize (provableStPC taut refl)
            :: derivSize (provablePC   taut refl)
            :: derivSize (provableStPC axT  refl)
            :: derivSize (provablePC   axT  refl)
            :: derivSize (provableStPC axX  refl)
            :: derivSize (provablePC   axX  refl) :: [])
              (7 :: 1 :: 55 :: 47 :: 149 :: 139 :: [])
c6_steps = refl

-- box p -> p, whole:

c6_axT : Eq (countOfPC axT) (prod 47 (prod 23 (prod 0 0)))
c6_axT = refl

-- and the formula the old certificate cannot print at all.  axX is
-- box (box p) -> box p, with |Sub (neg axX)| = 7; section 4g reports that it
-- did not finish in 280 s, and that nothing above |Sub| = 5 was printable.
-- Here it is 139 constructors, and every one of them is Lemma 2.6: three
-- eventualities at 46, plus the single line.  The certificate has become the
-- (S2) chain and nothing else.

c6_axX : Eq (length (sub (neg axX))
          :: derivSize (stateCompletePC (neg axX))
          :: length (boxArgs (sub (neg axX))) :: []) (7 :: 139 :: 3 :: [])
c6_axX = refl

c6_axX_count : Eq (countOfPC axX) (prod 139 (prod 69 (prod 0 0)))
c6_axX_count = refl

-- ONE (PC) node, whatever the formula.  Phase 9 had two -- Lemma 2.6 and (L5)
-- -- and G34 had 2 + |St P|, one per branch; collapsing the disjunction merges
-- all of them into the single line, so the whole appeal to the propositional
-- layer is made exactly once, which is exactly where Ben-Ari writes PC
-- (benari.pdf, Definition 12.1).  Everything else in a certificate is (T) --
-- once per eventuality -- and (Exp), (Ind), (Lin) inside extract.

c6_pc : Eq (pcOfPC taut :: pcOfPC axT :: pcOfPC axX :: []) (1 :: 1 :: 1 :: [])
c6_pc = refl

c6_states : Eq (length (St (neg taut)) :: length (St (neg axT))
             :: length (St (neg axX)) :: []) (2 :: 3 :: 4 :: [])
c6_states = refl

-- Lemma 2.6 for p -> p, printed in full.  Against 81363 constructors, the whole
-- proof that some state of St (neg taut) holds is one line carrying the formula
-- it proves -- which is what a Hilbert proof with Axiom 0 looks like.

c6_printed : Eq (showD 3 (stateCompletePC (neg taut)))
                (node rPc (beta (neg taut) (St (neg taut))) [])
c6_printed = refl

-- and the side condition of that line, RUN.  This is the cost section 7 warned
-- about, moved rather than removed: a pc node is one constructor, but isTaut
-- has to be evaluated before the node is accepted, and for a variable P it
-- never is -- tautState is a proof, not a refl, so typechecking the
-- development is unaffected.  Here the formulas are concrete, so the table can
-- be asked for directly: 2^|atoms| rows of  (S2) chain -> beta P (St P) , with
-- one, two and three atoms respectively.  It is checked by refl, which is what
-- the old certificate could not do at |Sub| = 7 in 280 s.

c6_rows : Eq (length (atomsOf (stateFml (neg taut)))
           :: length (atomsOf (stateFml (neg axT)))
           :: length (atomsOf (stateFml (neg axX))) :: []) (1 :: 2 :: 3 :: [])
c6_rows = refl

c6_side : Eq (isTaut (stateFml (neg taut)) :: isTaut (stateFml (neg axT))
           :: isTaut (stateFml (neg axX)) :: []) (true :: true :: true :: [])
c6_side = refl

-- G34's side conditions are the cheap ones, and it is worth saying why.  The
-- branch tautology  chi_w -> Q  contains chi_w, so it is a LONG formula -- 29
-- subformulas here against the branch derivation's 67 constructors -- but its
-- atoms are only the atoms of Sub (neg Q), because every conjunct of chi_w is a
-- literal of a subformula.  So the truth table has 2^|atoms| rows and not
-- 2^|Sub|, which is the same accounting as G30's: the length of a formula is
-- free, the number of independent atoms is what costs.

c6_branch_rows : Eq (length (atomsOf (imp (chi (neg taut) tautW) taut))
                  :: length (sub (imp (chi (neg taut) tautW) taut)) :: [])
                    (1 :: 29 :: [])
c6_branch_rows = refl

c6_branch_side : Eq (isTaut (imp (chi (neg taut) tautW) taut)) true
c6_branch_side = refl

-- Where the limit now is.  For the twenty-two-subformula example of section 4g --
-- box dia (p or q) -> box dia p or box dia q, decided in 0.9 s, whose old
-- Lemma 2.6 is a disjunction over 2^22 valuations and cannot be written down --
-- Lemma 2.6 alone is 277 constructors: six eventualities at 46 each, and one
-- line.
--
-- Its side condition used to be where the exponential went, and was NOT asked
-- for here: stateFml carries beta over St (neg axK5fwd), the states among
-- 2^22 vectors, so 2^8 rows of it is not a computation one starts.  Collapsing
-- the disjunction moves that too, and this is the part that was not expected.
-- remFml carries chi for the NINE removed states and nothing else, with the
-- same eight atoms, so the table is the same 2^8 rows of a formula that fits on
-- a page -- and it can simply be run.  Nine seconds, by refl, below.
--
-- So the trade Phase 9 recorded -- "the certificate is small and checking it is
-- not free; the two used to be the same number" -- is not the last word: what
-- made the certificate big and what made the side condition big were the same
-- disjunction, and removing it shrinks both.

c6_k5 : Eq (derivSize (stateCompletePC (neg axK5fwd))
         :: length (boxArgs (sub (neg axK5fwd))) :: []) (277 :: 6 :: [])
c6_k5 = refl

c6_k5_rem : Eq (length (removed (neg axK5fwd))
             :: length (StC (neg axK5fwd))
             :: length (atomsOf (remFml axK5fwd)) :: []) (9 :: 59 :: 8 :: [])
c6_k5_rem = refl

-- and the side condition of the certificate for axK5fwd, RUN.  This is the one
-- line in the file that takes seconds rather than milliseconds, and it is here
-- because it is the point: it is the check the old certificate could not make.

c6_k5_side : Eq (isTaut (remFml axK5fwd)) true
c6_k5_side = refl

------------------------------------------------------------------------
-- G35 of PHASE10-PLAN.md: chi over atoms, and the one trade that goes the
-- other way.
--
-- chi P v carries a literal for every position of Sub P, but (S1) determines
-- the bits at neg and imp from the bits at the atoms, so the non-atomic
-- literals are redundant.  chiA (LTL.ShortPC) keeps only the atomic ones, and
-- the bridge  neg chi_v -> neg chiA_v  is ONE (PC) node rather than the (S1)
-- induction PHASE10-PLAN.md expected: skelAgree says a row agreeing with a
-- state on the atoms agrees with it everywhere, so the implication holds under
-- every row and is a tautology of its own skeleton.
--
-- The certificate FORMULA shrinks by a factor of three -- for axK5fwd, 1956
-- subformula occurrences against 687, and 206 against 64 per removed state.
-- The NODE COUNT does not move at all: for a formula whose elimination removes
-- nothing there are no bridges and the two certificates are the same term, 1,
-- 47 and 139 below.
--
-- And the cost of CHECKING goes UP, which is the one place in the phase where
-- the trade reverses.  Measured, cold, on the axK5fwd side conditions:
--
--     isTaut (remFml  axK5fwd)          9.2 s     the chi certificate
--     isTaut (remFmlA axK5fwd)          8.0 s     the chiA certificate
--     the nine bridge conditions        9.2 s
--
-- so 17.2 s against 9.2 s.  The reason is structural and worth stating: chi
-- disappears from the main line only by reappearing in every bridge, and a
-- bridge mentions BOTH chi and chiA, so the total amount of chi in the side
-- conditions is not reduced at all -- it is multiplied by the number of rows a
-- second time.  Shrinking a formula that has to be evaluated 2^|atoms| times is
-- worth less than not evaluating it twice.
--
-- Both certificates are therefore kept and decidePC uses provablePC, the one
-- that is cheaper to CHECK rather than shorter to WRITE.  Which of those two is
-- the figure of merit depends on what a certificate is for, and the note does
-- not say; what can be done is to measure both, which is what this file is.

c7_chiA : Eq (length (sub (remFml  axK5fwd))
           :: length (sub (remFmlA axK5fwd)) :: []) (1956 :: 687 :: [])
c7_chiA = refl

c7_nodes : Eq (derivSize (provablePCA taut refl)
            :: derivSize (provablePCA axT  refl)
            :: derivSize (provablePCA axX  refl) :: []) (1 :: 47 :: 139 :: [])
c7_nodes = refl
