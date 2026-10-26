{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Taut -- G31 and G32 of FORMALISATION-PLAN.md, boolean half.
--
-- (PC) asks that a formula be a tautology of its own skeleton: isTaut A runs
-- valFrom over the truth table of atomsOf A (LTL.Skel).  The two formulas
-- Phase 9 wants to feed it are built by the list constructions of LTL.Val --
-- lit, conj, disj, chi and beta -- so what is needed is how valFrom reads
-- those, and that is all this module is.  No derivation appears in it.
--
-- Two things to keep in mind while reading, both of them warnings.
--
-- ONE ATOM LIST.  valFrom Ats a X depends on Ats: idx picks a FIRST occurrence,
-- so two atom lists give two different readings of the same formula and there
-- is no transport between them.  Every lemma here therefore takes Ats and a as
-- parameters and fixes them; each caller in LTL.CompletePC instantiates them
-- with atomsOf of the single formula its pc step is about, and nothing is ever
-- moved from one atom list to another.
--
-- NOT mkV.  LTL.Closure does the same construction with Ats := atoms (sub P) --
-- mkV, atomBits, valFromEq, mkV_id -- and those are the wrong lemmas here: the
-- atom list of a (PC) formula is a different, larger list, if only because
-- conj [] is top and so contributes var 0.  They would appear to typecheck and
-- then fail on an idx.  valOfMk below is the bridge that is actually wanted,
-- and it is one instance of atomLook.
--
-- The last section is the point.  Fix Ats and a; then
--
--     skelVec Ats a P  =  map (valFrom Ats a) (sub P)
--
-- is a STATE of P as soon as the (S2) instances hold under the same reading:
-- (S1) and coherence come for free, because valFrom is compositional on neg and
-- imp BY DEFINITION and because valOfMk makes the bit at a position depend on
-- the formula there rather than on the position.  That is the whole content of
-- the short Lemma 2.6, and the (S2) proviso is exactly the premise -- the E P
-- of section 7 -- that LTL.CompletePC discharges with |boxArgs| instances of
-- (T), one modus ponens each.

module LTL.Taut where

open import LTL.State public

------------------------------------------------------------------------
-- Booleans.
--
-- LTL.Sets has impIntroB and filter_true, but LTL.Sets is on the other branch
-- of the import graph -- above Step, where this module is below Proj -- so they
-- are unreachable from here and from LTL.Complete.  The three that are needed
-- are repeated under new names rather than moved, since moving them would drag
-- LTL.Reach under LTL.Complete.

boolSelf : (b : Bool) -> Eq (boolImp b b) true
boolSelf true  = refl
boolSelf false = refl

boolImpI : (x y : Bool) -> (Eq x true -> Eq y true) -> Eq (boolImp x y) true
boolImpI true  y h = h refl
boolImpI false y h = refl

boolImpR : (x y : Bool) -> Eq y true -> Eq (boolImp x y) true
boolImpR true  y e = e
boolImpR false y e = refl

boolEqRefl : (b : Bool) -> Eq (boolEq b b) true
boolEqRefl true  = refl
boolEqRefl false = refl

boolEqOf : (x y : Bool) -> Eq x y -> Eq (boolEq x y) true
boolEqOf x y refl = boolEqRefl x

filterIn : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
        -> Mem x xs -> Eq (p x) true -> Mem x (filterL p xs)
filterIn p []        ()        e
filterIn p (y :: ys) memHd     e = filterCons_hd (p y) y (filterL p ys) e
filterIn p (y :: ys) (memTl m) e =
  filterCons_mem (p y) y (filterL p ys) (filterIn p ys m e)

------------------------------------------------------------------------
-- Membership, as a boolean.
--
-- The converse of memF_tail: LTL.Skel proves what a true memF gives, and this
-- is what gives one.  It is what turns a Mem proof into the side condition of
-- atomLook, so it is the only thing standing between Mem A (sub P) and the
-- bridge below.

memF_mem : (As : List Formula) {A : Formula} -> Mem A As -> Eq (memF As A) true
memF_mem []        ()
memF_mem (B :: Bs) memHd     = orL (formEq B B) (memF Bs B) (formEq_refl B)
memF_mem (B :: Bs) {A} (memTl m) =
  orR (formEq B A) (memF Bs A) (memF_mem Bs m)

------------------------------------------------------------------------
-- The skeleton reads dis and con as one expects.
--
-- dis C D is imp (neg C) D and con C D is neg (imp C (neg D)), so these two are
-- boolean identities and not inductions; they are stated at the shapes the list
-- constructions produce, so that disjTrue and conjTrue below are two lines
-- each.

boolDisL : (x y : Bool) -> Eq x true -> Eq (boolImp (boolNot x) y) true
boolDisL true  y e = refl
boolDisL false y ()

boolConI : (x y : Bool) -> Eq x true -> Eq y true
        -> Eq (boolNot (boolImp x (boolNot y))) true
boolConI true  true  e1 e2 = refl
boolConI true  false e1 ()
boolConI false y     () e2

------------------------------------------------------------------------
-- disj and conj under the skeleton.
--
-- disj is true as soon as one disjunct is and conj as soon as all conjuncts
-- are.  The empty cases are the convention of Lemma 1.1: disj [] is bot, which
-- never has to be true, and conj [] is top, which is  var 0 -> var 0  and so
-- true by boolSelf whatever the atom list makes of var 0.

disjTrue : (Ats : List Formula) (a : Val) (Cs : List Formula) {C : Formula}
        -> Mem C Cs -> Eq (valFrom Ats a C) true
        -> Eq (valFrom Ats a (disj Cs)) true
disjTrue Ats a []        ()        e
disjTrue Ats a (D :: Cs) memHd     e =
  boolDisL (valFrom Ats a D) (valFrom Ats a (disj Cs)) e
disjTrue Ats a (D :: Cs) (memTl m) e =
  boolImpR (boolNot (valFrom Ats a D)) (valFrom Ats a (disj Cs))
           (disjTrue Ats a Cs m e)

conjTrue : (Ats : List Formula) (a : Val) (Cs : List Formula)
        -> ({C : Formula} -> Mem C Cs -> Eq (valFrom Ats a C) true)
        -> Eq (valFrom Ats a (conj Cs)) true
conjTrue Ats a []        h = boolSelf (valFrom Ats a (var zero))
conjTrue Ats a (D :: Cs) h =
  boolConI (valFrom Ats a D) (valFrom Ats a (conj Cs))
           (h memHd) (conjTrue Ats a Cs (\ m -> h (memTl m)))

------------------------------------------------------------------------
-- The characteristic formula of the row the assignment itself gives.
--
-- Read the atoms by a, read every formula of As by the skeleton, and collect
-- the answers: the literals of the resulting chi are true one by one, since
-- lit A true is A and lit A false is neg A and valFrom is boolNot at neg.  So
-- chi of that row is true -- which is the witness disjunct for both of the
-- tautologies of LTL.CompletePC.

litTrue : (Ats : List Formula) (a : Val) (A : Formula)
       -> Eq (valFrom Ats a (lit A (valFrom Ats a A))) true
litTrue Ats a A = go (valFrom Ats a A) refl
  where
    go : (b : Bool) -> Eq (valFrom Ats a A) b
      -> Eq (valFrom Ats a (lit A b)) true
    go true  e = e
    go false e = eqCong boolNot e

litListTrue : (Ats : List Formula) (a : Val) (As : List Formula) {C : Formula}
           -> Mem C (litList As (map (valFrom Ats a) As))
           -> Eq (valFrom Ats a C) true
litListTrue Ats a []        ()
litListTrue Ats a (A :: As) memHd     = litTrue Ats a A
litListTrue Ats a (A :: As) (memTl m) = litListTrue Ats a As m

chiRowTrue : (Ats : List Formula) (a : Val) (As : List Formula)
          -> Eq (valFrom Ats a (conj (litList As (map (valFrom Ats a) As)))) true
chiRowTrue Ats a As =
  conjTrue Ats a (litList As (map (valFrom Ats a) As))
           (\ m -> litListTrue Ats a As m)

------------------------------------------------------------------------
-- The bridge: the vector a truth-table row gives, read by valOf.
--
-- skelVec is mkV of LTL.Closure with the atom list left free, and valOfMk is
-- the corresponding valFromEq.  The proof is not an induction at all: valOf
-- looks a formula up by idx, skelVec is a map, and atomLook (LTL.Skel) is
-- exactly the round trip between those two, needing only that the formula
-- occurs -- which memF_mem supplies.

skelVec : List Formula -> Val -> Formula -> Val
skelVec Ats a P = map (valFrom Ats a) (sub P)

valOfMk : (P : Formula) (Ats : List Formula) (a : Val) (A : Formula)
       -> Mem A (sub P)
       -> Eq (valOf P (skelVec Ats a P) A) (valFrom Ats a A)
valOfMk P Ats a A m =
  atomLook (valFrom Ats a) (sub P) A (memF_mem (sub P) m)

------------------------------------------------------------------------
-- skelVec is a state, given (S2).
--
-- (S1) at neg and at imp, and coherence at every position, hold for no reason
-- at all: valOfMk says the bit at A is valFrom's reading of A, and valFrom IS
-- boolNot at neg and boolImp at imp.  This is the same observation that makes
-- the (PC) case of soundness one line (LTL.Sound) -- there against evalAt,
-- here against the vector's own valOf.
--
-- (S2) is the one clause that is not free, and it is not free because it is not
-- true of an arbitrary row: box A and A are two independent atoms of the
-- skeleton.  So it is assumed, as BoxOk, and the caller pays for it.

s2Fml : Formula -> Formula
s2Fml A = imp (box A) A

BoxOk : List Formula -> Val -> Formula -> Set
BoxOk Ats a P = (B : Formula) -> Mem (box B) (sub P)
             -> Eq (boolImp (valFrom Ats a (box B)) (valFrom Ats a B)) true

okAtSkel : (Ats : List Formula) (a : Val) (P : Formula) (A : Formula)
        -> Mem A (sub P) -> BoxOk Ats a P
        -> Eq (okAt P (skelVec Ats a P) A) true
okAtSkel Ats a P (var n)   m bo = refl
okAtSkel Ats a P (nxt B)   m bo = refl
okAtSkel Ats a P (neg B)   m bo =
  boolEqOf (valOf P (skelVec Ats a P) (neg B))
           (boolNot (valOf P (skelVec Ats a P) B))
           (eqTrans (valOfMk P Ats a (neg B) m)
                    (eqCong boolNot
                            (eqSym (valOfMk P Ats a B (sub_neg P m)))))
okAtSkel Ats a P (imp B C) m bo =
  boolEqOf (valOf P (skelVec Ats a P) (imp B C))
           (boolImp (valOf P (skelVec Ats a P) B) (valOf P (skelVec Ats a P) C))
           (eqTrans (valOfMk P Ats a (imp B C) m)
                    (eqCong2 boolImp
                             (eqSym (valOfMk P Ats a B (sub_impL P m)))
                             (eqSym (valOfMk P Ats a C (sub_impR P m)))))
okAtSkel Ats a P (box B)   m bo =
  eqTrans (eqCong2 boolImp (valOfMk P Ats a (box B) m)
                           (valOfMk P Ats a B (sub_box P m)))
          (bo B m)

allOkSkel : (Ats : List Formula) (a : Val) (P : Formula) (As : List Formula)
         -> ({A : Formula} -> Mem A As -> Mem A (sub P)) -> BoxOk Ats a P
         -> Eq (allOk P (skelVec Ats a P) As) true
allOkSkel Ats a P []        sb bo = refl
allOkSkel Ats a P (A :: As) sb bo =
  andIntro (okAt P (skelVec Ats a P) A) (allOk P (skelVec Ats a P) As)
           (okAtSkel Ats a P A (sb memHd) bo)
           (allOkSkel Ats a P As (\ m -> sb (memTl m)) bo)

-- Coherence.  The bit at position i is the skeleton's reading of the formula
-- AT position i, by nth_map, and the bit at the first occurrence of that same
-- formula is the same reading, by valOfMk.  So the two agree, which is what
-- cohAt asks; the vector represents a function on the SET Sub(P), which is the
-- clause of FORMALISATION-PLAN.md section 0.

ltUp : {i n : Nat} -> Lt i n -> Lt i (suc n)
ltUp ltZero    = ltZero
ltUp (ltSuc l) = ltSuc (ltUp l)

ltSucSelf : (n : Nat) -> Lt n (suc n)
ltSucSelf zero    = ltZero
ltSucSelf (suc n) = ltSuc (ltSucSelf n)

cohAtSkel : (Ats : List Formula) (a : Val) (P : Formula) (i : Nat)
         -> Lt i (length (sub P))
         -> Eq (cohAt P (skelVec Ats a P) i) true
cohAtSkel Ats a P i l =
  boolEqOf (bitAt (skelVec Ats a P) i)
           (valOf P (skelVec Ats a P) (nth (sub P) i bot))
           (eqTrans (nth_map (valFrom Ats a) (sub P) i l bot false)
                    (eqSym (valOfMk P Ats a (nth (sub P) i bot)
                                    (nth_mem (sub P) i l bot))))

allCohSkel : (Ats : List Formula) (a : Val) (P : Formula) (n : Nat)
          -> ((i : Nat) -> Lt i n -> Lt i (length (sub P)))
          -> Eq (allCoh P (skelVec Ats a P) n) true
allCohSkel Ats a P zero    h = refl
allCohSkel Ats a P (suc n) h =
  andIntro (cohAt P (skelVec Ats a P) n) (allCoh P (skelVec Ats a P) n)
           (cohAtSkel Ats a P n (h n (ltSucSelf n)))
           (allCohSkel Ats a P n (\ i l -> h i (ltUp l)))

isStateSkel : (Ats : List Formula) (a : Val) (P : Formula) -> BoxOk Ats a P
           -> Eq (isState P (skelVec Ats a P)) true
isStateSkel Ats a P bo =
  andIntro (allOk P (skelVec Ats a P) (sub P))
           (allCoh P (skelVec Ats a P) (length (sub P)))
           (allOkSkel Ats a P (sub P) (\ m -> m) bo)
           (allCohSkel Ats a P (length (sub P)) (\ i l -> l))

memStSkel : (Ats : List Formula) (a : Val) (P : Formula) -> BoxOk Ats a P
         -> Mem (skelVec Ats a P) (St P)
memStSkel Ats a P bo =
  filterIn (isState P) (allVecs (length (sub P)))
           (allVecs_complete (length (sub P)) (skelVec Ats a P)
                             (map_length (valFrom Ats a) (sub P)))
           (isStateSkel Ats a P bo)

------------------------------------------------------------------------
-- Hence beta_{St P} is true under any row satisfying (S2).
--
-- chi P (skelVec Ats a P) is one of its disjuncts, by memStSkel, and it is
-- true, by chiRowTrue at As := sub P.  That is Lemma 2.6 as a boolean fact,
-- and LTL.CompletePC turns it into a one-node derivation.

betaSkel : (Ats : List Formula) (a : Val) (P : Formula) -> BoxOk Ats a P
        -> Eq (valFrom Ats a (beta P (St P))) true
betaSkel Ats a P bo =
  disjTrue Ats a (map (chi P) (St P))
           (memMap (chi P) (memStSkel Ats a P bo))
           (chiRowTrue Ats a (sub P))

------------------------------------------------------------------------
-- The (S2) instances, discharged one at a time.
--
-- (S2) is assumed above, so it has to appear as a premise of the formula the
-- pc node proves.  section 7 makes it a CONJUNCTION over boxArgs (sub P); an
-- implication chain is better, and measurably so.  A conjunction has to be
-- built by (L2), and conjIntro goes through conPair, which goes through
-- negIntroU and dne: 239 constructors to conjoin a single instance of (T)
-- against the 47 the instance itself costs.  An iterated implication is
-- discharged by one modus ponens per premise, so the certificate is
--
--     |boxArgs (sub P)| * (1 + |boxElim|) + 1
--
-- exactly, with no propositional glue at all.  That is the linear-in-the-
-- eventualities figure the phase is after, and it is why conj does not appear
-- here even though the note's (L2) would have supplied it.
--
-- impChain is the boolean half, and it says the only thing an implication
-- chain ever says: reading it as true is the same as assuming its premises.
-- boxChain is that at As := map s2Fml (boxArgs (sub P)), where the premises are
-- (S2); the caller turns a box-subformula into a member with boxArgs_of.

impList : List Formula -> Formula -> Formula
impList []        C = C
impList (A :: As) C = imp A (impList As C)

impChain : (Ats : List Formula) (a : Val) (As : List Formula) (C : Formula)
        -> ((({A : Formula} -> Mem A As -> Eq (valFrom Ats a A) true)
              -> Eq (valFrom Ats a C) true))
        -> Eq (valFrom Ats a (impList As C)) true
impChain Ats a []        C h = h (\ ())
impChain Ats a (A :: As) C h =
  boolImpI (valFrom Ats a A) (valFrom Ats a (impList As C))
           (\ eA -> impChain Ats a As C (\ g -> h (more eA g)))
  where
    more : Eq (valFrom Ats a A) true
        -> ({X : Formula} -> Mem X As -> Eq (valFrom Ats a X) true)
        -> {X : Formula} -> Mem X (A :: As) -> Eq (valFrom Ats a X) true
    more eA g memHd     = eA
    more eA g (memTl m) = g m

S2At : List Formula -> Val -> List Formula -> Set
S2At Ats a As = (B : Formula) -> Mem B As
             -> Eq (boolImp (valFrom Ats a (box B)) (valFrom Ats a B)) true

boxChain : (Ats : List Formula) (a : Val) (As : List Formula) (C : Formula)
        -> (S2At Ats a As -> Eq (valFrom Ats a C) true)
        -> Eq (valFrom Ats a (impList (map s2Fml As) C)) true
boxChain Ats a As C h =
  impChain Ats a (map s2Fml As) C (\ g -> h (\ B mB -> g (memMap s2Fml mB)))

------------------------------------------------------------------------
-- (L5), as a boolean.
--
-- This is the same move again, one level down, and it is where the certificate
-- actually is.  disjElim (LTL.PropList) proves  (C1 or ... or Cn) -> C  from
-- the n implications Ci -> C, and it is the note's own (L5): dis A B is
-- neg A -> B, so the elimination has to contrapose and double-negate at every
-- cons, which measures 426 constructors PER DISJUNCT.  For the certificate that
-- is the dominant cost -- 1280 of the 1529 for box p -> p -- and it grows with
-- the number of states.
--
-- But the implication it proves is a tautology of its own skeleton, exactly as
-- Lemma 2.6's is, so it can be one pc node with the n branches discharged by
-- modus ponens.  What follows is its truth: given the premises and a true
-- disjunction, walk the disjunction until a true disjunct is found and use the
-- premise there.  The empty case is (L0) -- disj [] is bot, which cannot be
-- true, and boolSelf is what says so.

boolMP : (x y : Bool) -> Eq (boolImp x y) true -> Eq x true -> Eq y true
boolMP true  y e ex = e
boolMP false y e ()

impTo : Formula -> Formula -> Formula
impTo C D = imp D C

disjElimTrue : (Ats : List Formula) (a : Val) (Cs : List Formula) (C : Formula)
            -> ({D : Formula} -> Mem D Cs
                  -> Eq (valFrom Ats a (impTo C D)) true)
            -> Eq (valFrom Ats a (imp (disj Cs) C)) true
disjElimTrue Ats a Cs C h =
  boolImpI (valFrom Ats a (disj Cs)) (valFrom Ats a C) (go Cs h)
  where
    go : (Ds : List Formula)
      -> ({D : Formula} -> Mem D Ds -> Eq (valFrom Ats a (impTo C D)) true)
      -> Eq (valFrom Ats a (disj Ds)) true -> Eq (valFrom Ats a C) true
    go []        k e =
      emptyElim (tfAbs (eqTrans (eqSym e)
                                (eqCong boolNot
                                        (boolSelf (valFrom Ats a (var zero))))))
    go (D :: Ds) k e = onD (valFrom Ats a D) refl
      where
        onD : (b : Bool) -> Eq (valFrom Ats a D) b -> Eq (valFrom Ats a C) true
        onD true  eb = boolMP (valFrom Ats a D) (valFrom Ats a C) (k memHd) eb
        onD false eb =
          go Ds (\ m -> k (memTl m))
             (boolMP (boolNot (valFrom Ats a D)) (valFrom Ats a (disj Ds)) e
                     (eqCong boolNot eb))

------------------------------------------------------------------------
-- G34 of PHASE10-PLAN.md: the branch as one node.
--
-- The last term of the certificate that is neither constant nor linear-with-
-- constant-one is the 67 constructors per state -- the two easy cases of
-- provableEach, which project  neg neg Q  out of chi_w by (L2), 39, then
-- cancel the double negation, 23, then (L1), 5.
--
-- But  chi_w -> Q  is a TAUTOLOGY OF ITS OWN SKELETON whenever w does not
-- contain neg Q, and for the same reason the derivation works: chi_w is a
-- conjunction one of whose conjuncts is  lit (neg Q) (valOf (neg Q) w (neg Q))
-- -- and the hypothesis says that bit is false, so the conjunct is
-- neg (neg Q).  A conjunction implies its conjuncts, and valFrom is boolNot at
-- neg by definition, so a row making chi_w true makes  not not Q  true and
-- hence Q.  Nothing about Q's own structure is used; Q is read by the skeleton
-- like anything else.
--
-- So this is the same move as G31 and G32 one more time, at the last place it
-- had not been made: a propositional step DECIDED rather than derived.

------------------------------------------------------------------------
-- con, read out rather than built up.  boolConI above is the introduction; a
-- projection needs the two eliminations.

boolConE1 : (x y : Bool) -> Eq (boolNot (boolImp x (boolNot y))) true
         -> Eq x true
boolConE1 true  y e = refl
boolConE1 false y ()

boolConE2 : (x y : Bool) -> Eq (boolNot (boolImp x (boolNot y))) true
         -> Eq y true
boolConE2 true  true  e = refl
boolConE2 true  false ()
boolConE2 false y     ()

boolNotNot : (x : Bool) -> Eq (boolNot (boolNot x)) true -> Eq x true
boolNotNot true  e = refl
boolNotNot false ()

-- the converse of conjTrue: a true conjunction has true conjuncts

conjProjTrue : (Ats : List Formula) (a : Val) (Cs : List Formula) {C : Formula}
            -> Mem C Cs -> Eq (valFrom Ats a (conj Cs)) true
            -> Eq (valFrom Ats a C) true
conjProjTrue Ats a []        ()        e
conjProjTrue Ats a (D :: Cs) memHd     e =
  boolConE1 (valFrom Ats a D) (valFrom Ats a (conj Cs)) e
conjProjTrue Ats a (D :: Cs) (memTl m) e =
  conjProjTrue Ats a Cs m
               (boolConE2 (valFrom Ats a D) (valFrom Ats a (conj Cs)) e)

------------------------------------------------------------------------
-- The literal of P itself inside chi P w.
--
-- sub P begins with P (LTL.Sub) and formEq P P is true, so idx finds it at
-- position zero, which is also where sub_self points.  The five clauses are
-- the five clauses of sub_self, and each is the same one line: nothing is
-- proved by induction, only that the head of sub P is P.

idxSelf : (P : Formula) -> Eq (idx (sub P) P) (index (sub_self P))
idxSelf (var n)   = eqCong (\ b -> idxCons b (idx [] (var n))) (formEq_refl (var n))
idxSelf (neg A)   = eqCong (\ b -> idxCons b (idx (sub A) (neg A))) (formEq_refl (neg A))
idxSelf (imp A B) =
  eqCong (\ b -> idxCons b (idx (append (sub A) (sub B)) (imp A B)))
         (formEq_refl (imp A B))
idxSelf (nxt A)   = eqCong (\ b -> idxCons b (idx (sub A) (nxt A))) (formEq_refl (nxt A))
idxSelf (box A)   = eqCong (\ b -> idxCons b (idx (sub A) (box A))) (formEq_refl (box A))

litSelf : (P : Formula) (w : Val) -> Eq (length w) (length (sub P))
       -> Mem (lit P (valOf P w P)) (litList (sub P) w)
litSelf P w len =
  eqSubst (\ n -> Mem (lit P (bitAt w n)) (litList (sub P) w))
          (eqSym (idxSelf P))
          (litList_mem (sub P) w len (sub_self P))

------------------------------------------------------------------------
-- G34.
--
-- The state w is one of Sub (neg Q)'s valuations and it does not contain
-- neg Q; then  chi_w -> Q  is a skeleton tautology, so (PC) proves it in one
-- node where the projection-and-double-negation proof takes 67.

tautChi : (Q : Formula) (w : Val) -> Eq (length w) (length (sub (neg Q)))
       -> Eq (valOf (neg Q) w (neg Q)) false
       -> Eq (isTaut (imp (chi (neg Q) w) Q)) true
tautChi Q w len ev =
  allB_intro (\ a -> valFrom Ats a F) (allVecs (length Ats)) row
  where
    R : Formula
    R = neg Q

    F : Formula
    F = imp (chi R w) Q

    Ats : List Formula
    Ats = atomsOf F

    -- the conjunct  lit R false , i.e.  neg (neg Q)
    mneg : Mem (neg R) (litList (sub R) w)
    mneg = eqSubst (\ b -> Mem (lit R b) (litList (sub R) w)) ev (litSelf R w len)

    row : {a : Val} -> Mem a (allVecs (length Ats))
       -> Eq (valFrom Ats a F) true
    row {a} m = boolImpI (valFrom Ats a (chi R w)) (valFrom Ats a Q) step
      where
        step : Eq (valFrom Ats a (chi R w)) true -> Eq (valFrom Ats a Q) true
        step ec =
          boolNotNot (valFrom Ats a Q)
                     (conjProjTrue Ats a (litList (sub R) w) mneg ec)

------------------------------------------------------------------------
-- G35 of PHASE10-PLAN.md: chi over atoms, boolean half.
--
-- chi P v is a conjunction of |Sub P| literals where |atoms (sub P)| would do:
-- (S1) determines the bit at neg A from the bit at A and the bit at imp A B
-- from those at A and B, so the literals at the non-atomic positions are
-- redundant.  For neg (box p -> box nxt p) that is 7 conjuncts against 4, with
-- neg bnb listed twice and p twice; for neg axK5fwd it is 22 against 8.
--
-- What is needed to exploit that is one fact -- a row of the skeleton table
-- that agrees with a state on the ATOMS agrees with it everywhere -- and it is
-- skelEval (LTL.Skel) with the assignment left free instead of being map f Ats.
-- The five clauses are skelEval's five clauses; only the hypothesis changes.

notTrueT : (b : Bool) -> Eq (boolNot b) true -> Eq b false
notTrueT true  ()
notTrueT false e = refl

boolContra : (x y : Bool) -> (Eq y true -> Eq x true)
          -> Eq (boolImp (boolNot x) (boolNot y)) true
boolContra true  y     h = refl
boolContra false true  h = emptyElim (tfAbs (eqSym (h refl)))
boolContra false false h = refl

memF_sound : (As : List Formula) (A : Formula) -> Eq (memF As A) true -> Mem A As
memF_sound []        A ()
memF_sound (B :: Bs) A e = go (formEq B A) refl
  where
    go : (b : Bool) -> Eq (formEq B A) b -> Mem A (B :: Bs)
    go true  eb = eqSubst (\ X -> Mem X (B :: Bs)) (formEq_sound B A eb) memHd
    go false eb = memTl (memF_sound Bs A (memF_tail B Bs A e eb))

-- the atoms of a list are members of it

insFIn : (A : Formula) (Bs : List Formula) {X : Formula}
      -> Mem X (insF A Bs) -> Sum (Eq X A) (Mem X Bs)
insFIn A Bs {X} m = go (memF Bs A) refl
  where
    go : (b : Bool) -> Eq (memF Bs A) b -> Sum (Eq X A) (Mem X Bs)
    go true  e = inr (eqSubst (\ c -> Mem X (filterCons (boolNot c) A Bs)) e m)
    go false e = onM (eqSubst (\ c -> Mem X (filterCons (boolNot c) A Bs)) e m)
      where
        onM : Mem X (A :: Bs) -> Sum (Eq X A) (Mem X Bs)
        onM memHd     = inl refl
        onM (memTl k) = inr k

atomsIn : (As : List Formula) {X : Formula} -> Mem X (atoms As) -> Mem X As
atomsIn []              ()
atomsIn (var n   :: As) {X} m =
  sumElim (\ e -> eqSubst (\ Y -> Mem Y (var n :: As)) (eqSym e) memHd)
          (\ k -> memTl (atomsIn As k)) (insFIn (var n) (atoms As) m)
atomsIn (neg B   :: As)     m = memTl (atomsIn As m)
atomsIn (imp B C :: As)     m = memTl (atomsIn As m)
atomsIn (nxt B   :: As) {X} m =
  sumElim (\ e -> eqSubst (\ Y -> Mem Y (nxt B :: As)) (eqSym e) memHd)
          (\ k -> memTl (atomsIn As k)) (insFIn (nxt B) (atoms As) m)
atomsIn (box B   :: As) {X} m =
  sumElim (\ e -> eqSubst (\ Y -> Mem Y (box B :: As)) (eqSym e) memHd)
          (\ k -> memTl (atomsIn As k)) (insFIn (box B) (atoms As) m)

------------------------------------------------------------------------
-- Literals, read in both directions.

litOfEq : (Ats : List Formula) (a : Val) (A : Formula) (b : Bool)
       -> Eq (valFrom Ats a A) b -> Eq (valFrom Ats a (lit A b)) true
litOfEq Ats a A true  e = e
litOfEq Ats a A false e = eqCong boolNot e

litSound : (Ats : List Formula) (a : Val) (A : Formula) (b : Bool)
        -> Eq (valFrom Ats a (lit A b)) true -> Eq (valFrom Ats a A) b
litSound Ats a A true  e = e
litSound Ats a A false e = notTrueT (valFrom Ats a A) e

litMapMem : (f : Formula -> Bool) (As : List Formula) {X : Formula}
         -> Mem X As -> Mem (lit X (f X)) (litList As (map f As))
litMapMem f []        ()
litMapMem f (A :: As) memHd     = memHd
litMapMem f (A :: As) (memTl m) = memTl (litMapMem f As m)

litMapOk : (Ats : List Formula) (a : Val) (f : Formula -> Bool) (As : List Formula)
        -> ((A : Formula) -> Mem A As -> Eq (valFrom Ats a A) (f A))
        -> {C : Formula} -> Mem C (litList As (map f As))
        -> Eq (valFrom Ats a C) true
litMapOk Ats a f []        h ()
litMapOk Ats a f (A :: As) h memHd     = litOfEq Ats a A (f A) (h A memHd)
litMapOk Ats a f (A :: As) h (memTl m) =
  litMapOk Ats a f As (\ B mB -> h B (memTl mB)) m

------------------------------------------------------------------------
-- The fact G35 turns on.
--
-- A row that agrees with a state on the atoms of Sub P agrees with it on all of
-- Sub P.  This is skelEval with the assignment a free rather than map f Ats:
-- the induction is the same, and the two non-atomic clauses are (S1) read out
-- of allOk, exactly as valFromEq (LTL.Closure) does.

skelAgree : (Ats : List Formula) (a : Val) (P : Formula) (v : Val)
         -> Eq (allOk P v (sub P)) true
         -> ((X : Formula) -> Mem X (sub P) -> Eq (isAtomB X) true
               -> Eq (valFrom Ats a X) (valOf P v X))
         -> (A : Formula) -> Mem A (sub P)
         -> Eq (valFrom Ats a A) (valOf P v A)
skelAgree Ats a P v ok at (var n)   m = at (var n) m refl
skelAgree Ats a P v ok at (nxt A)   m = at (nxt A) m refl
skelAgree Ats a P v ok at (box A)   m = at (box A) m refl
skelAgree Ats a P v ok at (neg A)   m =
  eqTrans (eqCong boolNot (skelAgree Ats a P v ok at A (sub_neg P m)))
          (eqSym (boolEq_sound (valOf P v (neg A)) (boolNot (valOf P v A))
                               (allOk_at P v (sub P) m ok)))
skelAgree Ats a P v ok at (imp A B) m =
  eqTrans (eqCong2 boolImp (skelAgree Ats a P v ok at A (sub_impL P m))
                           (skelAgree Ats a P v ok at B (sub_impR P m)))
          (eqSym (boolEq_sound (valOf P v (imp A B))
                               (boolImp (valOf P v A) (valOf P v B))
                               (allOk_at P v (sub P) m ok)))
