{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Bar -- inductively finite sets, after Coquand and Siles, "A Decision
-- Procedure for Regular Expression Equivalence in Type Theory" (CPP 2011), §1.
--
--   Bar R E   holds when, starting from E and repeatedly picking an x and
--             passing to  E intersect (R x) , one always stops.
--
-- With R the complement of equality this says: one cannot go on choosing
-- DISTINCT elements of E forever.  That is exactly the principle the
-- development used to re-derive by hand, once per use, as a decreasing length.
-- Phase 8 (G29) replaces all of those by recursion on a Bar: shrinkGo
-- (LTL.Gfp), elimGo (LTL.Elim), lassoSearch (LTL.Lasso), and then closeGo
-- (LTL.Closure), which is G30 and which no length would have justified at all.
--
-- Subsets are taken DECIDABLE, as boolean predicates, rather than as
-- Prop-valued ones.  Everything this development quantifies over is decidable,
-- and it keeps Bar in Set rather than Set1.
--
-- Two suppliers of Bars are provided and they are used for different things.
--
--   barOfList / listBar -- a Kuratowski finite list gives a Bar.  Right when
--     the search removes from a list that is already in hand and whose length
--     one is willing to pay for once: W_0 in LTL.Gfp, U_inf in LTL.Lasso.
--
--   vecIFin / guardedVecBar -- the vectors of a given length are inductively
--     finite, by induction on the length, in O(n) rather than 2^n.  Right when
--     there is no such list: the elimination, which is not to force
--     length (Ust P) merely to bound itself, and above all the closure of
--     LTL.Closure, which GROWS and so has no decreasing measure at all.
--
-- The second is the useful direction and the hard one: the paper notes that the
-- product lemma is essentially the proof that a product of well-quasi-orderings
-- is one.

module LTL.Bar where

open import LTL.Sets public

------------------------------------------------------------------------
-- Bar

data Bar {A : Set} (R : A -> A -> Bool) : (A -> Bool) -> Set where
  cBar : {E : A -> Bool}
      -> ((x : A) -> Eq (E x) true
            -> Bar R (\ y -> boolAnd (E y) (R x y)))
      -> Bar R E

-- The recursion principle.  Every "keep going until you run out" argument in
-- the development is this with a different C.
barRec : {A : Set} {R : A -> A -> Bool} (C : (A -> Bool) -> Set)
      -> ({E : A -> Bool}
            -> ((x : A) -> Eq (E x) true -> C (\ y -> boolAnd (E y) (R x y)))
            -> C E)
      -> {E : A -> Bool} -> Bar R E -> C E
barRec C f (cBar h) = f (\ x ex -> barRec C f (h x ex))

barStep : {A : Set} (R : A -> A -> Bool) (E F : A -> Bool)
       -> ((x : A) -> Eq (E x) true -> Eq (F x) true)
       -> (x y : A) -> Eq (boolAnd (E y) (R x y)) true
       -> Eq (boolAnd (F y) (R x y)) true
barStep R E F sb x y e =
  andIntro (F y) (R x y) (sb y (andTrueL (E y) (R x y) e))
                         (andTrueR (E y) (R x y) e)

barMono : {A : Set} {R : A -> A -> Bool} {E F : A -> Bool}
       -> ((x : A) -> Eq (E x) true -> Eq (F x) true)
       -> Bar R F -> Bar R E
barMono {R = R} {E = E} {F = F} sb (cBar h) =
  cBar (\ x ex -> barMono (barStep R E F sb x) (h x (sb x ex)))

------------------------------------------------------------------------
-- Inductive finiteness for valuations

neqB : Val -> Val -> Bool
neqB x y = boolNot (valEq x y)

neqB_self : (x : Val) -> Eq (neqB x x) false
neqB_self x = eqCong boolNot (valEq_refl x)

IFin : (Val -> Bool) -> Set
IFin E = Bar neqB E

------------------------------------------------------------------------
-- Kuratowski implies inductively finite.
--
-- The Le measure of the development survives here and nowhere else: it is paid
-- once, when the Bar is built, and no search counts anything afterwards.

barOfList : {E : Val -> Bool} (n : Nat) (xs : List Val) -> Le (length xs) n
         -> ((x : Val) -> Eq (E x) true -> Mem x xs) -> IFin E
barOfList         zero    xs le sb =
  cBar (\ x ex -> emptyElim (leZeroNil xs le (sb x ex)))
barOfList {E = E} (suc n) xs le sb =
  cBar (\ x ex -> barOfList n (filterL (neqB x) xs)
                    (lePred (leTrans (filterL_lt (neqB x) xs (sb x ex)
                                                 (neqB_self x)) le))
                    (\ z ez -> filter_true (neqB x) xs
                                 (sb z (andTrueL (E z) (neqB x z) ez))
                                 (andTrueR (E z) (neqB x z) ez)))

------------------------------------------------------------------------
-- Boolean glue for the two closure lemmas

taut1 : (g h t : Bool) -> Eq (boolAnd (boolOr g h) t) true
     -> Eq (boolOr (boolAnd g t) (boolAnd h t)) true
taut1 true  h true  e = refl
taut1 true  h false ()
taut1 false h t     e = e

taut2 : (g h t : Bool) -> Eq (boolAnd (boolOr g h) t) true
     -> Eq (boolOr g (boolAnd h t)) true
taut2 true  h t e = refl
taut2 false h t e = e

taut3 : (e f r s : Bool)
     -> Eq (boolAnd (boolAnd e f) (boolOr r s)) true
     -> Eq (boolOr (boolAnd (boolAnd e r) f) (boolAnd e (boolAnd f s))) true
taut3 true  true  true  s h = refl
taut3 true  true  false s h = h
taut3 true  false r     s ()
taut3 false f     r     s ()

------------------------------------------------------------------------
-- Union.  Lemma 1, second bullet.
--
-- Double induction: on the first witness for the G-case, on the second for
-- the H-case.  barMono does the work that would otherwise need funext, since
-- Bar is indexed by the predicate and the two sides are only pointwise equal.

barUnion : {A : Set} {T : A -> A -> Bool} {G H : A -> Bool}
        -> Bar T G -> Bar T H -> Bar T (\ y -> boolOr (G y) (H y))
barUnion {A} {T} {G} {H} (cBar hg) bh = inner H bh
  where
    inner : (H' : A -> Bool) -> Bar T H' -> Bar T (\ y -> boolOr (G y) (H' y))
    inner H' (cBar hh) = cBar pick
      where
        pick : (x : A) -> Eq (boolOr (G x) (H' x)) true
            -> Bar T (\ y -> boolAnd (boolOr (G y) (H' y)) (T x y))
        pick x ex = sumElim fromG fromH (orTrue (G x) (H' x) ex)
          where
            fromG : Eq (G x) true
                 -> Bar T (\ y -> boolAnd (boolOr (G y) (H' y)) (T x y))
            fromG eg =
              barMono (\ y ey -> taut1 (G y) (H' y) (T x y) ey)
                      (barUnion (hg x eg)
                                (barMono (\ y ey -> andTrueL (H' y) (T x y) ey)
                                         (cBar hh)))

            fromH : Eq (H' x) true
                 -> Bar T (\ y -> boolAnd (boolOr (G y) (H' y)) (T x y))
            fromH eh =
              barMono (\ y ey -> taut2 (G y) (H' y) (T x y) ey)
                      (inner (\ y -> boolAnd (H' y) (T x y)) (hh x eh))

------------------------------------------------------------------------
-- Product.  Lemma 1, fourth bullet -- the load-bearing one.

prodPred : {A B : Set} -> (A -> Bool) -> (B -> Bool) -> Prod A B -> Bool
prodPred E F (prod x y) = boolAnd (E x) (F y)

prodRel : {A B : Set} -> (A -> A -> Bool) -> (B -> B -> Bool)
       -> Prod A B -> Prod A B -> Bool
prodRel R S (prod x y) (prod u v) = boolOr (R x u) (S y v)

prodMono : {A B : Set} (R : A -> A -> Bool) (S : B -> B -> Bool)
           (E : A -> Bool) (F : B -> Bool) (x : A) (y : B) (q : Prod A B)
        -> Eq (boolAnd (prodPred E F q) (prodRel R S (prod x y) q)) true
        -> Eq (boolOr (prodPred (\ a -> boolAnd (E a) (R x a)) F q)
                      (prodPred E (\ b -> boolAnd (F b) (S y b)) q)) true
prodMono R S E F x y (prod u v) e = taut3 (E u) (F v) (R x u) (S y v) e

barProd : {A B : Set} {R : A -> A -> Bool} {S : B -> B -> Bool}
       -> {E : A -> Bool} {F : B -> Bool}
       -> Bar R E -> Bar S F -> Bar (prodRel R S) (prodPred E F)
barProd {A} {B} {R} {S} {E} {F} (cBar he) bf = inner F bf
  where
    inner : (F' : B -> Bool) -> Bar S F'
         -> Bar (prodRel R S) (prodPred E F')
    inner F' (cBar hf) = cBar pick
      where
        pick : (p : Prod A B) -> Eq (prodPred E F' p) true
            -> Bar (prodRel R S)
                   (\ q -> boolAnd (prodPred E F' q) (prodRel R S p q))
        pick (prod x y) ep =
          barMono (prodMono R S E F' x y)
                  (barUnion (barProd (he x (andTrueL (E x) (F' y) ep)) (cBar hf))
                            (inner (\ b -> boolAnd (F' b) (S y b))
                                   (hf y (andTrueR (E x) (F' y) ep))))

------------------------------------------------------------------------
-- Pulling back along a map that reflects the relation on a domain D

barPull : {A B : Set} {R : A -> A -> Bool} {S : B -> B -> Bool}
       -> (f : B -> A) (D : B -> Bool)
       -> ((y z : B) -> Eq (D y) true -> Eq (D z) true -> Eq (S y z) true
             -> Eq (R (f y) (f z)) true)
       -> {E : A -> Bool} -> Bar R E
       -> Bar S (\ y -> boolAnd (D y) (E (f y)))
barPull {A} {B} {R} {S} f D h {E} (cBar hE) = cBar pick
  where
    pick : (y : B) -> Eq (boolAnd (D y) (E (f y))) true
        -> Bar S (\ z -> boolAnd (boolAnd (D z) (E (f z))) (S y z))
    pick y ey =
      barMono keep (barPull f D h (hE (f y) (andTrueR (D y) (E (f y)) ey)))
      where
        keep : (z : B) -> Eq (boolAnd (boolAnd (D z) (E (f z))) (S y z)) true
            -> Eq (boolAnd (D z) (boolAnd (E (f z)) (R (f y) (f z)))) true
        keep z ez =
          andIntro (D z) (boolAnd (E (f z)) (R (f y) (f z)))
                   (andTrueL (D z) (E (f z))
                             (andTrueL (boolAnd (D z) (E (f z))) (S y z) ez))
                   (andIntro (E (f z)) (R (f y) (f z))
                             (andTrueR (D z) (E (f z))
                                       (andTrueL (boolAnd (D z) (E (f z))) (S y z) ez))
                             (h y z (andTrueL (D y) (E (f y)) ey)
                                    (andTrueL (D z) (E (f z))
                                              (andTrueL (boolAnd (D z) (E (f z)))
                                                        (S y z) ez))
                                    (andTrueR (boolAnd (D z) (E (f z))) (S y z) ez)))

------------------------------------------------------------------------
-- Bool is inductively finite

neqBool : Bool -> Bool -> Bool
neqBool a b = boolNot (boolEq a b)

bool3 : (x y z : Bool) -> Eq (neqBool x y) true -> Eq (neqBool x z) true
     -> Eq (neqBool y z) true -> Empty
bool3 true  true  z     () e2 e3
bool3 true  false true  e1 () e3
bool3 true  false false e1 e2 ()
bool3 false false z     () e2 e3
bool3 false true  false e1 () e3
bool3 false true  true  e1 e2 ()

boolIFin : Bar neqBool (\ b -> true)
boolIFin =
  cBar (\ x ex ->
  cBar (\ y ey ->
  cBar (\ z ez ->
    emptyElim (bool3 x y z ey
                 (andTrueL (neqBool x z) (neqBool y z) ez)
                 (andTrueR (neqBool x z) (neqBool y z) ez)))))

------------------------------------------------------------------------
-- Vectors of a given length are inductively finite -- in O(n), not 2^n.
--
-- This is the point of the file.  A valuation of length n+1 is a Bool paired
-- with a valuation of length n, so barProd applies, and barPull transports the
-- result back along uncons.  The recursion is on n; allVecs never appears.

lenB : Nat -> Val -> Bool
lenB n v = natEq (length v) n

headV : Val -> Bool
headV []       = false
headV (b :: v) = b

tailV : Val -> Val
tailV []       = []
tailV (b :: v) = v

unconsV : Val -> Prod Bool Val
unconsV v = prod (headV v) (tailV v)

lenZero : (v : Val) -> Eq (natEq (length v) zero) true -> Eq v []
lenZero []       e = refl
lenZero (b :: v) ()

lenTail : (m : Nat) (v : Val) -> Eq (lenB (suc m) v) true
       -> Eq (lenB m (tailV v)) true
lenTail m []       ()
lenTail m (b :: v) e = e

deMorgan : (a b : Bool) -> Eq (boolNot (boolAnd a b)) true
        -> Eq (boolOr (boolNot a) (boolNot b)) true
deMorgan true  true  ()
deMorgan true  false e = refl
deMorgan false b     e = refl

unconsNeq : (m : Nat) (y z : Val) -> Eq (lenB (suc m) y) true
         -> Eq (lenB (suc m) z) true -> Eq (neqB y z) true
         -> Eq (prodRel neqBool neqB (unconsV y) (unconsV z)) true
unconsNeq m []       z        () ez e
unconsNeq m (b :: v) []       ey () e
unconsNeq m (b :: v) (c :: w) ey ez e = deMorgan (boolEq b c) (valEq v w) e

vecIFin : (n : Nat) -> IFin (lenB n)
vecIFin zero =
  cBar (\ x ex -> cBar (\ y ey ->
    emptyElim (clash x y ex (andTrueL (lenB zero y) (neqB x y) ey)
                            (andTrueR (lenB zero y) (neqB x y) ey))))
  where
    clash : (x y : Val) -> Eq (lenB zero x) true -> Eq (lenB zero y) true
         -> Eq (neqB x y) true -> Empty
    clash x y ex ey e = tfAbs (eqSym nil2)
      where
        -- both are [], and neqB [] [] is false
        nil2 : Eq (neqB [] []) true
        nil2 = eqSubst (\ u -> Eq (neqB u []) true) (lenZero x ex)
                       (eqSubst (\ u -> Eq (neqB x u) true) (lenZero y ey) e)
vecIFin (suc m) =
  barMono (\ v ev -> andIntro (lenB (suc m) v)
                              (prodPred (\ b -> true) (lenB m) (unconsV v))
                              ev (lenTail m v ev))
          (barPull unconsV (lenB (suc m)) (unconsNeq m)
                   (barProd boolIFin (vecIFin m)))


------------------------------------------------------------------------
-- The invariant the removing searches carry.
--
-- InE E xs says the list xs lies inside the predicate E.  A search that
-- removes an element x from xs passes to E intersect (R x), and that is
-- precisely the sub-Bar cBar hands over -- so the "pool" of section 4c of
-- FORMALISATION-PLAN.md is no longer a list carried alongside the search: it
-- is the Bar's own predicate.

InE : (Val -> Bool) -> List Val -> Set
InE E xs = (x : Val) -> Mem x xs -> Eq (E x) true

memInE : (xs : List Val) -> InE (\ v -> memB v xs) xs
memInE xs x m = memB_complete x xs m

listBar : (xs : List Val) -> IFin (\ v -> memB v xs)
listBar xs = barOfList (length xs) xs (leRefl (length xs))
                       (\ x ex -> memB_sound x xs ex)

-- Dropping x from the list is dropping x from the predicate.  Both searches of
-- G29 that remove a member of the list they are searching use this.

dropInE : {E : Val -> Bool} (p : Val -> Bool) (xs : List Val) -> InE E xs
       -> (x : Val) -> Eq (p x) false
       -> InE (\ y -> boolAnd (E y) (neqB x y)) (filterL p xs)
dropInE {E} p xs sb x q z mz =
  andIntro (E z) (neqB x z)
           (sb z (filter_sub p xs mz))
           (eqCong boolNot (onEq (valEq x z) refl))
  where
    onEq : (b : Bool) -> Eq (valEq x z) b -> Eq (valEq x z) false
    onEq false e = e
    onEq true  e =
      emptyElim (tfAbs (eqTrans (eqSym (eqSubst (\ u -> Eq (p u) true)
                                                (eqSym (valEq_sound x z e))
                                                (filter_prop p xs mz)))
                                q))

------------------------------------------------------------------------
-- Members of allVecs n have length n.
--
-- Needed to hand guardedVecBar the states: St P is a subset of allVecs
-- (length (sub P)), so the length-n predicate is a correct E for it, and then
-- the search never touches the enumeration.

map_mem_inv : {A B : Set} (f : A -> B) (xs : List A) {y : B}
           -> Mem y (map f xs) -> Sigma A (\ x -> Prod (Mem x xs) (Eq y (f x)))
map_mem_inv f []        ()
map_mem_inv f (x :: xs) memHd     = sig x (prod memHd refl)
map_mem_inv f (x :: xs) (memTl m) = shift (map_mem_inv f xs m)
  where
    shift : Sigma _ (\ z -> Prod (Mem z xs) _) -> Sigma _ (\ z -> Prod (Mem z (x :: xs)) _)
    shift (sig z (prod mz ez)) = sig z (prod (memTl mz) ez)

allVecs_len : (n : Nat) {v : Val} -> Mem v (allVecs n) -> Eq (lenB n v) true
allVecs_len zero    memHd      = refl
allVecs_len zero    (memTl ())
allVecs_len (suc n) m =
  sumElim (fromHalf true) (fromHalf false)
          (memAppCase (map (\ bs -> true  :: bs) (allVecs n))
                      (map (\ bs -> false :: bs) (allVecs n)) m)
  where
    fromHalf : {v : Val} (b : Bool) -> Mem v (map (\ bs -> b :: bs) (allVecs n))
            -> Eq (lenB (suc n) v) true
    fromHalf {v} b mv = fromSig (map_mem_inv (\ bs -> b :: bs) (allVecs n) mv)
      where
        fromSig : Sigma Val (\ w -> Prod (Mem w (allVecs n)) (Eq v (b :: w)))
               -> Eq (lenB (suc n) v) true
        fromSig (sig w (prod mw ew)) =
          eqSubst (\ u -> Eq (lenB (suc n) u) true) (eqSym ew) (allVecs_len n mw)

stInE : (P : Formula) -> InE (lenB (length (sub P))) (St P)
stInE P x m =
  allVecs_len (length (sub P))
              (filter_sub (isState P) (allVecs (length (sub P))) m)

------------------------------------------------------------------------
-- The guard of Barras, refined by Gonthier (siles.pdf, section 5).
--
-- The paper's point is that one computes with the decision procedure DIRECTLY,
-- as a type-theoretic boolean function, without extracting to ML.  It also
-- records the price: a function defined by recursion on a well-foundedness
-- proof forces that proof as it runs, "and this computation is heavy, and
-- furthermore seems irrelevant, since the accessibility predicate has only one
-- constructor".
--
-- Their fix transfers, and the reason it transfers is worth stating.  Barras's
-- guard works on `well_founded`, a Pi-type, so a guarded proof can produce a
-- constructor without ever applying the proof it wraps.  Bar R E at a FIXED E
-- is a tree, not a function, and admits no such trick -- but vecIFin gives the
-- Pi-form we need, since every subset of the length-n vectors is Bar by
-- barMono.  guardBar k then supplies 2^k constructors lazily, so a search of
-- depth below 2^k never touches vecIFin at all.

AllBar : Nat -> Set
AllBar n = (E : Val -> Bool)
        -> ((v : Val) -> Eq (E v) true -> Eq (lenB n v) true) -> IFin E

allVecBar : (n : Nat) -> AllBar n
allVecBar n E sb = barMono sb (vecIFin n)

guardBar : (n k : Nat) -> AllBar n -> AllBar n
guardBar n zero    w = w
guardBar n (suc k) w =
  \ E sb -> cBar (\ x ex ->
    guardBar n k (guardBar n k w)
             (\ y -> boolAnd (E y) (neqB x y))
             (\ v ev -> sb v (andTrueL (E v) (neqB x v) ev)))

-- The guard depth is n itself, and that is not a cosmetic choice.
--
-- Two things fix it.  A search that keeps choosing DISTINCT vectors of length n
-- runs for at most 2^n steps, and guardBar n k supplies 2^k constructors, so
-- k = n is exactly enough: for |Sub P| = 13 the guard alone carries 8192 peels
-- and vecIFin is never reached.
--
-- More importantly, a literal depth is unusable.  guardBar n k unfolds to 2^k
-- copies of what it wraps, so with k a literal the NORMAL FORM of the guarded
-- Bar has 2^k nodes -- and Agda normalises the constructor types of a data
-- declaration, so every data type whose constructors mention U_infinity (Succ,
-- Escape, Walk, Round, Lasso, Run, ValidPos: most of Phases 5 and 6) would
-- normalise it.  With k = n and P a variable the match on k is blocked, the
-- guard stays folded, and the explosion cannot happen; on a closed formula n
-- reduces and the guard does its job.  Laziness has to be arranged in the term,
-- not merely relied on in the evaluator.

guardedVecBar : (n : Nat) -> AllBar n
guardedVecBar n = guardBar n n (allVecBar n)
