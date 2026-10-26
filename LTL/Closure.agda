{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Closure -- G30 of FORMALISATION-PLAN.md: the set the SEARCH explores, as
-- opposed to the list the DERIVATIONS quantify over.
--
-- Until Phase 8 those were the same object, St P.  They should not be.
--
--   St P is  filterL (isState P) (allVecs |Sub P|) , and it has to stay that
--   way: state completeness (G17) is proved by splitting the disjunction over
--   ALL 2^|Sub P| valuations and then dropping the non-states, so  beta (St P)
--   being a theorem IS the fact that the state set is complete.  That term is
--   typechecked and never normalised, so its 2^|Sub P| costs nothing.
--
--   The elimination, Theorem 4.1 and the lasso, on the other hand, ARE
--   normalised -- computing with the decision procedure directly is the point
--   (siles.pdf section 6) -- and they do not need every state.  They need a set
--   U of states that is closed under ->-successors and contains every state
--   containing P, and nothing else.
--
-- This module builds such a U and proves the three properties, ustSt, ustSeed
-- and ustClosed, that everything downstream is stated against.
--
-- Why exactly those three.  ustClosed is what case (R1) of Theorem 4.1 needs:
-- the step lemma offers ALL state-successors of u, and each has to be either
-- already refuted or still inside the set being eliminated.  ustSeed is what
-- the provable branch needs: a state outside U cannot contain P, so by (S1) it
-- contains neg P and chi_w yields the conclusion with no elimination at all.
-- ustSt keeps every member of U a state.
--
-- U is built in two steps.
--
-- 1. The candidates.  A state is not an arbitrary vector: (S1) determines the
--    bit at  neg A  and at  imp A B  from the bits at A and at B, and coherence
--    makes the bit depend on the formula rather than on the position.  So a
--    state is determined by its bits at the ATOMS of Sub P -- the var, nxt and
--    box entries -- and mkV builds the whole vector from such an assignment.
--    That replaces 2^|Sub P| candidates by 2^|atoms|; for the C5 formula, 8192
--    by 128.  stcSt and stStc show the resulting StC P has exactly the members
--    of St P, so nothing is lost and nothing is gained but speed.
--
-- 2. The closure.  U need not be all of StC P either: it is enough to take the
--    ->-closure of the states containing P.  That is a LEAST fixed point, the
--    one place in the development where the removing iteration of section 4b
--    does not apply -- the accumulator grows -- and it is why Bar is needed
--    rather than another decreasing length.  Each round adds a state that was
--    not there before, so the vectors chosen are distinct, and vecIFin says one
--    cannot go on choosing distinct vectors of length n forever.

module LTL.Closure where

open import LTL.Bar public

------------------------------------------------------------------------
-- Extensionality for bit vectors, and the assignment a state induces.
--
-- Everything else this module used to define -- memF, insF, atoms, valFrom and
-- the idx/nth round-trip -- moved down to LTL.Skel when (PC) needed it below
-- Deriv.  The skeleton evaluation is shared with the tautology test, which is
-- the point: mkV builds a state from a truth-table row.

valExt : (v w : Val) -> Eq (length v) (length w)
      -> ((i : Nat) -> Lt i (length v) -> Eq (bitAt v i) (bitAt w i)) -> Eq v w
valExt []       []       e  h = refl
valExt []       (c :: w) () h
valExt (b :: v) []       () h
valExt (b :: v) (c :: w) e  h =
  eqCons (h zero ltZero) (valExt v w (sucInj e) (\ i l -> h (suc i) (ltSuc l)))

------------------------------------------------------------------------
-- The vector an assignment to the atoms determines, and the assignment a
-- state induces

mkV : Formula -> Val -> Val
mkV P a = map (valFrom (atoms (sub P)) a) (sub P)

atomBits : Formula -> Val -> Val
atomBits P v = map (valOf P v) (atoms (sub P))

------------------------------------------------------------------------
-- A state is the vector its own atom bits determine.
--
-- This used to be a five-case induction on the formula.  It is now one
-- instance of skelEval (LTL.Skel): valOf at a state is a COMPOSITIONAL reading
-- of formulas, which is exactly what (S1) says, and skelEval says any such
-- reading agrees with the skeleton evaluation.  The other instance of the same
-- lemma is the soundness of (PC) in LTL.Sound, where the two hypotheses are
-- refl because evalAt is defined by boolNot and boolImp.

valFromEq : (P : Formula) (v : Val) -> Eq (allOk P v (sub P)) true
         -> (A : Formula) -> Mem A (sub P)
         -> Eq (valFrom (atoms (sub P)) (atomBits P v) A) (valOf P v A)
valFromEq P v ok =
  skelEval (valOf P v) (atoms (sub P)) P
           (\ X mX aX -> atomMem (sub P) mX aX)
           (\ X mX -> boolEq_sound (valOf P v (neg X)) (boolNot (valOf P v X))
                                   (allOk_at P v (sub P) mX ok))
           (\ X Y mX -> boolEq_sound (valOf P v (imp X Y))
                                     (boolImp (valOf P v X) (valOf P v Y))
                                     (allOk_at P v (sub P) mX ok))

mkV_id : (P : Formula) (v : Val) -> Eq (isState P v) true
      -> Eq (length v) (length (sub P)) -> Eq (mkV P (atomBits P v)) v
mkV_id P v st len = valExt (mkV P (atomBits P v)) v lenEq pointwise
  where
    ok : Eq (allOk P v (sub P)) true
    ok = andTrueL (allOk P v (sub P)) (allCoh P v (length (sub P))) st

    coh : Eq (allCoh P v (length (sub P))) true
    coh = andTrueR (allOk P v (sub P)) (allCoh P v (length (sub P))) st

    lenEq : Eq (length (mkV P (atomBits P v))) (length v)
    lenEq = eqTrans (map_length (valFrom (atoms (sub P)) (atomBits P v)) (sub P))
                    (eqSym len)

    pointwise : (i : Nat) -> Lt i (length (mkV P (atomBits P v)))
             -> Eq (bitAt (mkV P (atomBits P v)) i) (bitAt v i)
    pointwise i l = eqTrans (eqTrans atI (valFromEq P v ok (nth (sub P) i bot) mI))
                            (eqSym cohI)
      where
        lI : Lt i (length (sub P))
        lI = eqSubst (\ k -> Lt i k)
                     (map_length (valFrom (atoms (sub P)) (atomBits P v)) (sub P)) l

        mI : Mem (nth (sub P) i bot) (sub P)
        mI = nth_mem (sub P) i lI bot

        atI : Eq (bitAt (mkV P (atomBits P v)) i)
                 (valFrom (atoms (sub P)) (atomBits P v) (nth (sub P) i bot))
        atI = nth_map (valFrom (atoms (sub P)) (atomBits P v)) (sub P) i lI bot false

        cohI : Eq (bitAt v i) (valOf P v (nth (sub P) i bot))
        cohI = boolEq_sound (bitAt v i) (valOf P v (nth (sub P) i bot))
                            (allCoh_at P v (length (sub P)) i lI coh)

------------------------------------------------------------------------
-- The candidates, and the state list they give

cands : Formula -> List Val
cands P = map (mkV P) (allVecs (length (atoms (sub P))))

candsLen : (P : Formula) {v : Val} -> Mem v (cands P)
        -> Eq (length v) (length (sub P))
candsLen P {v} m =
  fromSig (map_mem_inv (mkV P) (allVecs (length (atoms (sub P)))) m)
  where
    fromSig : Sigma Val (\ a -> Prod (Mem a (allVecs (length (atoms (sub P)))))
                                     (Eq v (mkV P a)))
           -> Eq (length v) (length (sub P))
    fromSig (sig a (prod ma ea)) =
      eqTrans (eqCong length ea)
              (map_length (valFrom (atoms (sub P)) a) (sub P))

StC : Formula -> List Val
StC P = filterL (isState P) (cands P)

stcSt : (P : Formula) {v : Val} -> Mem v (StC P) -> Mem v (St P)
stcSt P {v} m =
  filter_true (isState P) (allVecs (length (sub P)))
              (allVecs_complete (length (sub P)) v
                                (candsLen P (filter_sub (isState P) (cands P) m)))
              (filter_prop (isState P) (cands P) m)

stStc : (P : Formula) {v : Val} -> Mem v (St P) -> Mem v (StC P)
stStc P {v} m = filter_true (isState P) (cands P) inCands st
  where
    st : Eq (isState P v) true
    st = filter_prop (isState P) (allVecs (length (sub P))) m

    len : Eq (length v) (length (sub P))
    len = allVecs_len' (length (sub P)) v
                       (filter_sub (isState P) (allVecs (length (sub P))) m)
      where
        allVecs_len' : (n : Nat) (w : Val) -> Mem w (allVecs n) -> Eq (length w) n
        allVecs_len' n w mw = natEq_sound (length w) n (allVecs_len n mw)

    inCands : Mem v (cands P)
    inCands =
      eqSubst (\ z -> Mem z (cands P)) (mkV_id P v st len)
              (memMap (mkV P)
                      (allVecs_complete (length (atoms (sub P))) (atomBits P v)
                                        (map_length (valOf P v) (atoms (sub P)))))

------------------------------------------------------------------------
-- The ->-closure of the states containing P.
--
-- Step 2.  The accumulator acc starts empty and each round adds every state of
-- StC P that is WANTED -- contains P, or is a ->-successor of something already
-- in acc -- and is not there yet.  When a round finds nothing to add, acc
-- contains every wanted state, which is ustSeed and ustClosed together.
--
-- This is the one search in the development that GROWS, so the removing
-- iteration of FORMALISATION-PLAN.md section 4b does not apply and there is no
-- decreasing length to run on.  What there is instead: each round adds at least
-- one state that was not there before, that state is a vector of length
-- |Sub P|, and one cannot go on choosing distinct vectors of a fixed length
-- forever.  That is vecIFin exactly, guarded so that it is not forced as the
-- search runs, and it is why Bar is needed here and not merely convenient.

vecBar : (P : Formula) -> IFin (lenB (length (sub P)))
vecBar P = guardedVecBar (length (sub P)) (lenB (length (sub P))) (\ v ev -> ev)

wanted : Formula -> List Val -> Val -> Bool
wanted P acc v = boolOr (valOf P v P) (anyL (\ u -> step P u v) acc)

missing : Formula -> List Val -> Val -> Bool
missing P acc v = boolAnd (wanted P acc v) (boolNot (memB v acc))

okAcc : Formula -> List Val -> Val -> Bool
okAcc P acc v = boolNot (missing P acc v)

addAll : Formula -> List Val -> List Val
addAll P acc = append (filterL (missing P acc) (StC P)) acc

-- Reading okAcc in both directions

okAccIn : (w n : Bool) -> Eq (boolNot (boolAnd w n)) true -> Eq w true -> Eq n false
okAccIn true  true  () e
okAccIn true  false q  e = refl
okAccIn false n     q  ()

missingOf : (P : Formula) (acc : List Val) (x : Val) -> Eq (okAcc P acc x) false
         -> Eq (missing P acc x) true
missingOf P acc x q = notFalse (missing P acc x) q

notInAcc : (P : Formula) (acc : List Val) (x : Val) -> Eq (okAcc P acc x) false
        -> Eq (memB x acc) false
notInAcc P acc x q =
  notTrue (memB x acc)
          (andTrueR (wanted P acc x) (boolNot (memB x acc)) (missingOf P acc x q))

inAddAll : (P : Formula) (acc : List Val) (x : Val) -> Mem x (StC P)
        -> Eq (okAcc P acc x) false -> Mem x (addAll P acc)
inAddAll P acc x m q =
  memAppL (filterL (missing P acc) (StC P)) acc
          (filter_true (missing P acc) (StC P) m (missingOf P acc x q))

------------------------------------------------------------------------
-- The search

closeGo   : (P : Formula) {E : Val -> Bool} (acc : List Val)
         -> ((z : Val) -> Mem z (StC P) -> Eq (memB z acc) false -> Eq (E z) true)
         -> IFin E -> List Val
closeFind : (P : Formula) {E : Val -> Bool} (acc : List Val)
         -> ((z : Val) -> Mem z (StC P) -> Eq (memB z acc) false -> Eq (E z) true)
         -> IFin E -> FindResult (okAcc P acc) (StC P) -> List Val

closeGo P acc av bar = closeFind P acc av bar (findFalse (okAcc P acc) (StC P))

closeFind P acc av bar      (allT f)      = acc
closeFind P {E} acc av (cBar h) (found x m q) =
  closeGo P (addAll P acc) av' (h x (av x m (notInAcc P acc x q)))
  where
    av' : (z : Val) -> Mem z (StC P) -> Eq (memB z (addAll P acc)) false
       -> Eq (boolAnd (E z) (neqB x z)) true
    av' z mz e =
      andIntro (E z) (neqB x z)
               (av z mz (outAcc (memB z acc) refl))
               (eqCong boolNot (outX (valEq x z) refl))
      where
        outAcc : (b : Bool) -> Eq (memB z acc) b -> Eq (memB z acc) false
        outAcc false eb = eb
        outAcc true  eb =
          emptyElim (memB_false z (addAll P acc) e
                      (memAppR (filterL (missing P acc) (StC P)) acc
                               (memB_sound z acc eb)))

        outX : (b : Bool) -> Eq (valEq x z) b -> Eq (valEq x z) false
        outX false eb = eb
        outX true  eb =
          emptyElim (memB_false z (addAll P acc) e
                      (eqSubst (\ y -> Mem y (addAll P acc)) (valEq_sound x z eb)
                               (inAddAll P acc x m q)))

------------------------------------------------------------------------
-- Its three properties, each by the same recursion

closeGoSt   : (P : Formula) {E : Val -> Bool} (acc : List Val)
           -> (av : (z : Val) -> Mem z (StC P) -> Eq (memB z acc) false
                  -> Eq (E z) true)
           -> (bar : IFin E)
           -> ((z : Val) -> Mem z acc -> Mem z (StC P))
           -> {z : Val} -> Mem z (closeGo P acc av bar) -> Mem z (StC P)
closeFindSt : (P : Formula) {E : Val -> Bool} (acc : List Val)
           -> (av : (z : Val) -> Mem z (StC P) -> Eq (memB z acc) false
                  -> Eq (E z) true)
           -> (bar : IFin E) (fr : FindResult (okAcc P acc) (StC P))
           -> ((z : Val) -> Mem z acc -> Mem z (StC P))
           -> {z : Val} -> Mem z (closeFind P acc av bar fr) -> Mem z (StC P)

closeGoSt P acc av bar =
  closeFindSt P acc av bar (findFalse (okAcc P acc) (StC P))

closeFindSt P acc av bar      (allT f)      sb {z} m = sb z m
closeFindSt P acc av (cBar h) (found x mx q) sb    m =
  closeGoSt P (addAll P acc) _ (h x (av x mx (notInAcc P acc x q))) sb' m
  where
    sb' : (z : Val) -> Mem z (addAll P acc) -> Mem z (StC P)
    sb' z mz = sumElim (\ m1 -> filter_sub (missing P acc) (StC P) m1)
                       (\ m2 -> sb z m2)
                       (memAppCase (filterL (missing P acc) (StC P)) acc mz)

closeGoSeed   : (P : Formula) {E : Val -> Bool} (acc : List Val)
             -> (av : (z : Val) -> Mem z (StC P) -> Eq (memB z acc) false
                    -> Eq (E z) true)
             -> (bar : IFin E) {z : Val}
             -> Mem z (StC P) -> Eq (valOf P z P) true
             -> Mem z (closeGo P acc av bar)
closeFindSeed : (P : Formula) {E : Val -> Bool} (acc : List Val)
             -> (av : (z : Val) -> Mem z (StC P) -> Eq (memB z acc) false
                    -> Eq (E z) true)
             -> (bar : IFin E) (fr : FindResult (okAcc P acc) (StC P)) {z : Val}
             -> Mem z (StC P) -> Eq (valOf P z P) true
             -> Mem z (closeFind P acc av bar fr)

closeGoSeed P acc av bar =
  closeFindSeed P acc av bar (findFalse (okAcc P acc) (StC P))

closeFindSeed P acc av bar      (allT f)       {z} mz e =
  memB_sound z acc
    (notFalse (memB z acc)
              (okAccIn (wanted P acc z) (boolNot (memB z acc)) (f mz)
                       (orL (valOf P z P) (anyL (\ u -> step P u z) acc) e)))
closeFindSeed P acc av (cBar h) (found x mx q)     mz e =
  closeGoSeed P (addAll P acc) _ (h x (av x mx (notInAcc P acc x q))) mz e

closeGoClosed   : (P : Formula) {E : Val -> Bool} (acc : List Val)
               -> (av : (z : Val) -> Mem z (StC P) -> Eq (memB z acc) false
                      -> Eq (E z) true)
               -> (bar : IFin E) {u w : Val}
               -> Mem u (closeGo P acc av bar) -> Mem w (StC P)
               -> Eq (step P u w) true -> Mem w (closeGo P acc av bar)
closeFindClosed : (P : Formula) {E : Val -> Bool} (acc : List Val)
               -> (av : (z : Val) -> Mem z (StC P) -> Eq (memB z acc) false
                      -> Eq (E z) true)
               -> (bar : IFin E) (fr : FindResult (okAcc P acc) (StC P)) {u w : Val}
               -> Mem u (closeFind P acc av bar fr) -> Mem w (StC P)
               -> Eq (step P u w) true -> Mem w (closeFind P acc av bar fr)

closeGoClosed P acc av bar =
  closeFindClosed P acc av bar (findFalse (okAcc P acc) (StC P))

closeFindClosed P acc av bar      (allT f)       {u} {w} mu mw st =
  memB_sound w acc
    (notFalse (memB w acc)
              (okAccIn (wanted P acc w) (boolNot (memB w acc)) (f mw)
                       (orR (valOf P w P) (anyL (\ u' -> step P u' w) acc)
                            (anyL_intro (\ u' -> step P u' w) acc mu st))))
closeFindClosed P acc av (cBar h) (found x mx q)      mu mw st =
  closeGoClosed P (addAll P acc) _ (h x (av x mx (notInAcc P acc x q))) mu mw st

------------------------------------------------------------------------
-- The set the search explores, and its three properties

StFrom : Formula -> List Val
StFrom P = closeGo P [] (\ z mz e -> stInE P z (stcSt P mz)) (vecBar P)

emptyAcc : (P : Formula) (z : Val) -> Mem z ([] {A = Val}) -> Mem z (StC P)
emptyAcc P z ()

Ust : Formula -> List Val
Ust P = StFrom P

ustSt : (P : Formula) {v : Val} -> Mem v (Ust P) -> Mem v (St P)
ustSt P m =
  stcSt P (closeGoSt P [] (\ z mz e -> stInE P z (stcSt P mz)) (vecBar P)
                     (emptyAcc P) m)

ustSeed : (P : Formula) {v : Val}
       -> Mem v (St P) -> Eq (valOf P v P) true -> Mem v (Ust P)
ustSeed P m e =
  closeGoSeed P [] (\ z mz e' -> stInE P z (stcSt P mz)) (vecBar P) (stStc P m) e

ustClosed : (P : Formula) {v w : Val}
         -> Mem v (Ust P) -> Mem w (St P) -> Eq (step P v w) true -> Mem w (Ust P)
ustClosed P mv mw st =
  closeGoClosed P [] (\ z mz e -> stInE P z (stcSt P mz)) (vecBar P)
                mv (stStc P mw) st

ustInE : (P : Formula) -> InE (lenB (length (sub P))) (Ust P)
ustInE P x m = stInE P x (ustSt P m)

ustBar : (P : Formula) -> IFin (lenB (length (sub P)))
ustBar P = vecBar P
