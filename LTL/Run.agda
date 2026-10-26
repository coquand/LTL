{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Run -- the lasso unwound, as the finite structure G24 and G25 run on.
--
-- m4.tex unwinds a lasso into the infinite sequence v_0,v_1,v_2,... with
-- v_i = v_{p+((i-p) mod (q-p))} for i >= p, and then says: "the lasso is a
-- finite structure with a total successor function, so Always and Eventually
-- evaluate on it by conjunction and disjunction over the finite forward orbit
-- of a state".
--
-- Taken literally that asks for indices into a flat list of states, a successor
-- function  k |-> k+1 wrapping at the end, and a forward orbit obtained by
-- iterating it -- and then for arithmetic: that consecutive indices step, that
-- the wrap lands on the right index, that the orbit from any index covers the
-- whole cycle.  That is the index bookkeeping section 3 of the plan warned
-- about, and none of it is necessary.
--
-- A POSITION is instead a pair (s , rest): the current state, and the states
-- still to come before the cycle starts again.  The successor is
--
--    (s , w :: ws)  |->  (w , ws)          walk on
--    (s , [])       |->  (c0 , c1)         wrap to the head of the cycle
--
-- and a position is VALID when rest is a walk from s back to the cycle's end b.
-- Validity is preserved by the successor, and the step proof falls out of the
-- Walk constructor being consumed: no arithmetic at all.  Better still, the
-- forward orbit of (s , rest), with the fuel that is obviously enough, is
-- LITERALLY  posList s rest ++ posList c0 c1  -- walk out the remaining rest,
-- then walk once round the cycle -- which is orbitP_split below, proved by a
-- three-line induction.  Everything G24 needs about orbits follows from that
-- one equation by memAppL and memAppR.

module LTL.Run where

open import LTL.Lasso public

------------------------------------------------------------------------
-- Addition

plus : Nat -> Nat -> Nat
plus zero    n = n
plus (suc m) n = suc (plus m n)

plus_zero : (m : Nat) -> Eq (plus m zero) m
plus_zero zero    = refl
plus_zero (suc m) = eqCong suc (plus_zero m)

------------------------------------------------------------------------
-- Positions and the successor function

Pos : Set
Pos = Prod Val (List Val)

posState : Pos -> Val
posState (prod s rest) = s

nextPos : Val -> List Val -> Pos -> Pos
nextPos c0 c1 (prod s [])        = prod c0 c1
nextPos c0 c1 (prod s (w :: ws)) = prod w ws

posIter : Val -> List Val -> Nat -> Pos -> Pos
posIter c0 c1 zero    pos = pos
posIter c0 c1 (suc i) pos = posIter c0 c1 i (nextPos c0 c1 pos)

posIter_plus : (c0 : Val) (c1 : List Val) (i t : Nat) (pos : Pos)
            -> Eq (posIter c0 c1 (plus i t) pos)
                  (posIter c0 c1 t (posIter c0 c1 i pos))
posIter_plus c0 c1 zero    t pos = refl
posIter_plus c0 c1 (suc i) t pos = posIter_plus c0 c1 i t (nextPos c0 c1 pos)

------------------------------------------------------------------------
-- Valid positions.
--
-- rest is a walk from s back to b, the end of the cycle.  This is the whole
-- invariant; the transition relation of the run is a consequence of it.

data ValidPos (P : Formula) (b : Val) : Pos -> Set where
  vpos : (s : Val) (rest : List Val) -> Mem s (Uinf P)
      -> Walk P (Uinf P) s rest b -> ValidPos P b (prod s rest)

posStep : (P : Formula) (b c0 : Val) (c1 : List Val)
       -> Mem c0 (Uinf P) -> Walk P (Uinf P) c0 c1 b -> Eq (step P b c0) true
       -> {pos : Pos} -> ValidPos P b pos
       -> Prod (ValidPos P b (nextPos c0 c1 pos))
               (Eq (step P (posState pos) (posState (nextPos c0 c1 pos))) true)
posStep P b c0 c1 mc0 wc stb (vpos s []        ms wnil) =
  prod (vpos c0 c1 mc0 wc) stb
posStep P b c0 c1 mc0 wc stb (vpos s (w :: ws) ms (wcons mw st wk)) =
  prod (vpos w ws mw wk) st

posIn : (P : Formula) (b : Val) {pos : Pos}
     -> ValidPos P b pos -> Mem (posState pos) (Uinf P)
posIn P b (vpos s rest ms wk) = ms

------------------------------------------------------------------------
-- The forward orbit

posList : Val -> List Val -> List Pos
posList s []        = prod s [] :: []
posList s (w :: ws) = prod s (w :: ws) :: posList w ws

orbitP : Val -> List Val -> Nat -> Pos -> List Pos
orbitP c0 c1 zero    pos = []
orbitP c0 c1 (suc n) pos = pos :: orbitP c0 c1 n (nextPos c0 c1 pos)

-- The equation everything rests on.
orbitP_split : (c0 : Val) (c1 : List Val) (s : Val) (rest : List Val) (n : Nat)
            -> Eq (orbitP c0 c1 (suc (plus (length rest) n)) (prod s rest))
                  (append (posList s rest) (orbitP c0 c1 n (prod c0 c1)))
orbitP_split c0 c1 s []        n = refl
orbitP_split c0 c1 s (w :: ws) n =
  eqCong (\ L -> prod s (w :: ws) :: L) (orbitP_split c0 c1 w ws n)

orbitOf : Val -> List Val -> Pos -> List Pos
orbitOf c0 c1 (prod s rest) =
  orbitP c0 c1 (suc (plus (length rest) (suc (length c1)))) (prod s rest)

cycOrbit : (c0 : Val) (c1 : List Val)
        -> Eq (orbitP c0 c1 (suc (length c1)) (prod c0 c1))
              (append (posList c0 c1) [])
cycOrbit c0 c1 =
  eqSubst (\ k -> Eq (orbitP c0 c1 (suc k) (prod c0 c1))
                     (append (posList c0 c1) []))
          (plus_zero (length c1))
          (orbitP_split c0 c1 c0 c1 zero)

orbitStem : (c0 : Val) (c1 : List Val) (s : Val) (rest : List Val) (q : Pos)
         -> Mem q (posList s rest) -> Mem q (orbitOf c0 c1 (prod s rest))
orbitStem c0 c1 s rest q m =
  eqSubst (\ L -> Mem q L)
          (eqSym (orbitP_split c0 c1 s rest (suc (length c1))))
          (memAppL (posList s rest) (orbitP c0 c1 (suc (length c1)) (prod c0 c1)) m)

orbitCycle : (c0 : Val) (c1 : List Val) (s : Val) (rest : List Val) (q : Pos)
          -> Mem q (posList c0 c1) -> Mem q (orbitOf c0 c1 (prod s rest))
orbitCycle c0 c1 s rest q m =
  eqSubst (\ L -> Mem q L)
          (eqSym (orbitP_split c0 c1 s rest (suc (length c1))))
          (memAppR (posList s rest) (orbitP c0 c1 (suc (length c1)) (prod c0 c1))
                   (eqSubst (\ L -> Mem q L) (eqSym (cycOrbit c0 c1))
                            (memAppL (posList c0 c1) [] m)))

-- A state visited on a stretch is the state of a position on it.

posShift : {s w : Val} {ws : List Val} {z : Val}
        -> Sigma Pos (\ q -> Prod (Mem q (posList w ws)) (Eq (posState q) z))
        -> Sigma Pos (\ q -> Prod (Mem q (posList s (w :: ws))) (Eq (posState q) z))
posShift (sig q (prod mq eq)) = sig q (prod (memTl mq) eq)

posList_mem : (s : Val) (rest : List Val) {z : Val} -> Mem z (s :: rest)
           -> Sigma Pos (\ q -> Prod (Mem q (posList s rest)) (Eq (posState q) z))
posList_mem s []        memHd     = sig (prod s []) (prod memHd refl)
posList_mem s []        (memTl ())
posList_mem s (w :: ws) memHd     = sig (prod s (w :: ws)) (prod memHd refl)
posList_mem s (w :: ws) (memTl m) = posShift (posList_mem w ws m)

-- Every position of an orbit is reached from its start by iterating.

posBump : {c0 : Val} {c1 : List Val} {pos q : Pos}
       -> Sigma Nat (\ t -> Eq (posIter c0 c1 t (nextPos c0 c1 pos)) q)
       -> Sigma Nat (\ t -> Eq (posIter c0 c1 t pos) q)
posBump (sig t e) = sig (suc t) e

orbitP_iter : (c0 : Val) (c1 : List Val) (n : Nat) (pos q : Pos)
           -> Mem q (orbitP c0 c1 n pos)
           -> Sigma Nat (\ t -> Eq (posIter c0 c1 t pos) q)
orbitP_iter c0 c1 zero    pos q ()
orbitP_iter c0 c1 (suc n) pos q memHd     = sig zero refl
orbitP_iter c0 c1 (suc n) pos q (memTl m) =
  posBump (orbitP_iter c0 c1 n (nextPos c0 c1 pos) q m)

orbitOf_iter : (c0 : Val) (c1 : List Val) (pos q : Pos)
            -> Mem q (orbitOf c0 c1 pos)
            -> Sigma Nat (\ t -> Eq (posIter c0 c1 t pos) q)
orbitOf_iter c0 c1 (prod s rest) q m =
  orbitP_iter c0 c1 (suc (plus (length rest) (suc (length c1)))) (prod s rest) q m

------------------------------------------------------------------------
-- The run, extracted from a lasso.
--
-- The cycle is split once and for all into its head c0 and tail c1, which is
-- what makes nextPos total; the lasso's Eq (nullB qs) false is what licenses
-- the split, and that in turn is what the extra step of roundOf bought.

data Run (P : Formula) (v0 : Val) : Set where
  mkRun : (b c0 : Val) (c1 : List Val)
       -> Mem c0 (Uinf P)
       -> Walk P (Uinf P) c0 c1 b
       -> Eq (step P b c0) true
       -> Mem b (c0 :: c1)
       -> ((s : Val) -> Mem s (b :: c0 :: c1)
             -> (A : Formula) -> Mem A (boxArgs (sub P))
             -> Eq (valOf P s (box A)) false -> Fulfil P A b (c0 :: c1))
       -> (rest : List Val) -> Mem v0 (Uinf P) -> Walk P (Uinf P) v0 rest b
       -> Run P v0

runOf : (P : Formula) (v0 : Val) -> Mem v0 (Uinf P) -> Lasso P v0 -> Run P v0
runOf P v0 mv0 (mkLasso b mb ps wp []        wq () cyc)
runOf P v0 mv0 (mkLasso b mb ps wp (q :: qs) (wcons mq st wqs) nn cyc) =
  mkRun b q qs mq wqs st (walkEnd P (Uinf P) wqs) cyc
        (append ps (q :: qs)) mv0
        (walkApp P (Uinf P) wp (wcons mq st wqs))

runStart : (P : Formula) (v0 : Val) -> Run P v0 -> Pos
runStart P v0 (mkRun b c0 c1 mc0 wc stb mbc cyc rest mv0 wr) = prod v0 rest

runValid : (P : Formula) (v0 : Val) (r : Run P v0) -> Set
runValid P v0 (mkRun b c0 c1 mc0 wc stb mbc cyc rest mv0 wr) =
  ValidPos P b (prod v0 rest)

runStartValid : (P : Formula) (v0 : Val) (r : Run P v0) -> runValid P v0 r
runStartValid P v0 (mkRun b c0 c1 mc0 wc stb mbc cyc rest mv0 wr) =
  vpos v0 rest mv0 wr

------------------------------------------------------------------------
-- The orbit, once more, as a plain concatenation.
--
-- Everything below is read off this equation: the orbit of (s , rest) is the
-- rest of the walk followed by one turn of the cycle.

append_nil : {A : Set} (xs : List A) -> Eq (append xs []) xs
append_nil []        = refl
append_nil (x :: xs) = eqCong (\ zs -> x :: zs) (append_nil xs)

orbitEq : (c0 : Val) (c1 : List Val) (s : Val) (rest : List Val)
       -> Eq (orbitOf c0 c1 (prod s rest))
             (append (posList s rest) (posList c0 c1))
orbitEq c0 c1 s rest =
  eqTrans (orbitP_split c0 c1 s rest (suc (length c1)))
          (eqCong (\ L -> append (posList s rest) L)
                  (eqTrans (cycOrbit c0 c1) (append_nil (posList c0 c1))))

orbitHead : (c0 : Val) (c1 : List Val) (pos : Pos) -> Mem pos (orbitOf c0 c1 pos)
orbitHead c0 c1 (prod s rest) = memHd

posList_hd : (s : Val) (rest : List Val) -> Mem (prod s rest) (posList s rest)
posList_hd s []        = memHd
posList_hd s (w :: ws) = memHd

------------------------------------------------------------------------
-- The orbit is closed under the successor.
--
-- Walking on stays inside the same stretch until the stretch runs out, and
-- then lands on the head of the cycle, which is in the orbit either way.

posList_next : (c0 : Val) (c1 : List Val) (s : Val) (rest : List Val) (q : Pos)
            -> Mem q (posList s rest)
            -> Sum (Mem (nextPos c0 c1 q) (posList s rest))
                   (Eq (nextPos c0 c1 q) (prod c0 c1))
posList_next c0 c1 s []        q memHd     = inr refl
posList_next c0 c1 s []        q (memTl ())
posList_next c0 c1 s (w :: ws) q memHd     = inl (memTl (posList_hd w ws))
posList_next c0 c1 s (w :: ws) q (memTl m) =
  sumElim (\ mm -> inl (memTl mm)) inr (posList_next c0 c1 w ws q m)

orbitClosed : (c0 : Val) (c1 : List Val) (pos q : Pos)
           -> Mem q (orbitOf c0 c1 pos) -> Mem (nextPos c0 c1 q) (orbitOf c0 c1 pos)
orbitClosed c0 c1 (prod s rest) q m =
  eqSubst (\ L -> Mem (nextPos c0 c1 q) L) (eqSym (orbitEq c0 c1 s rest))
          (sumElim onStem onCyc
                   (memAppCase (posList s rest) (posList c0 c1)
                               (eqSubst (\ L -> Mem q L) (orbitEq c0 c1 s rest) m)))
  where
    intoCyc : Eq (nextPos c0 c1 q) (prod c0 c1)
           -> Mem (nextPos c0 c1 q) (append (posList s rest) (posList c0 c1))
    intoCyc e =
      eqSubst (\ r -> Mem r (append (posList s rest) (posList c0 c1))) (eqSym e)
              (memAppR (posList s rest) (posList c0 c1) (posList_hd c0 c1))

    onStem : Mem q (posList s rest)
          -> Mem (nextPos c0 c1 q) (append (posList s rest) (posList c0 c1))
    onStem mq = sumElim (\ mm -> memAppL (posList s rest) (posList c0 c1) mm)
                        intoCyc (posList_next c0 c1 s rest q mq)

    onCyc : Mem q (posList c0 c1)
         -> Mem (nextPos c0 c1 q) (append (posList s rest) (posList c0 c1))
    onCyc mq = sumElim (\ mm -> memAppR (posList s rest) (posList c0 c1) mm)
                       intoCyc (posList_next c0 c1 c0 c1 q mq)

posIter_suc : (c0 : Val) (c1 : List Val) (t : Nat) (pos : Pos)
           -> Eq (posIter c0 c1 (suc t) pos) (nextPos c0 c1 (posIter c0 c1 t pos))
posIter_suc c0 c1 zero    pos = refl
posIter_suc c0 c1 (suc t) pos = posIter_suc c0 c1 t (nextPos c0 c1 pos)

orbitIter : (c0 : Val) (c1 : List Val) (t : Nat) (pos : Pos)
         -> Mem (posIter c0 c1 t pos) (orbitOf c0 c1 pos)
orbitIter c0 c1 zero    pos = orbitHead c0 c1 pos
orbitIter c0 c1 (suc t) pos =
  eqSubst (\ r -> Mem r (orbitOf c0 c1 pos)) (eqSym (posIter_suc c0 c1 t pos))
          (orbitClosed c0 c1 pos (posIter c0 c1 t pos) (orbitIter c0 c1 t pos))

-- so the orbit of a successor is contained in the orbit
orbitSub : (c0 : Val) (c1 : List Val) (pos q : Pos)
        -> Mem q (orbitOf c0 c1 (nextPos c0 c1 pos)) -> Mem q (orbitOf c0 c1 pos)
orbitSub c0 c1 pos q m = fromIter (orbitOf_iter c0 c1 (nextPos c0 c1 pos) q m)
  where
    fromIter : Sigma Nat (\ t -> Eq (posIter c0 c1 t (nextPos c0 c1 pos)) q)
            -> Mem q (orbitOf c0 c1 pos)
    fromIter (sig t et) =
      eqSubst (\ r -> Mem r (orbitOf c0 c1 pos)) et (orbitIter c0 c1 (suc t) pos)

------------------------------------------------------------------------
-- Validity is preserved along the run, hence throughout an orbit

posIterValid : (P : Formula) (b c0 : Val) (c1 : List Val)
            -> Mem c0 (Uinf P) -> Walk P (Uinf P) c0 c1 b -> Eq (step P b c0) true
            -> (t : Nat) (pos : Pos) -> ValidPos P b pos
            -> ValidPos P b (posIter c0 c1 t pos)
posIterValid P b c0 c1 mc0 wc stb zero    pos vp = vp
posIterValid P b c0 c1 mc0 wc stb (suc t) pos vp =
  posIterValid P b c0 c1 mc0 wc stb t (nextPos c0 c1 pos)
               (prodFst (posStep P b c0 c1 mc0 wc stb vp))

orbitValid : (P : Formula) (b c0 : Val) (c1 : List Val)
          -> Mem c0 (Uinf P) -> Walk P (Uinf P) c0 c1 b -> Eq (step P b c0) true
          -> (pos q : Pos) -> ValidPos P b pos -> Mem q (orbitOf c0 c1 pos)
          -> ValidPos P b q
orbitValid P b c0 c1 mc0 wc stb pos q vp m =
  fromIter (orbitOf_iter c0 c1 pos q m)
  where
    fromIter : Sigma Nat (\ t -> Eq (posIter c0 c1 t pos) q) -> ValidPos P b q
    fromIter (sig t et) =
      eqSubst (\ r -> ValidPos P b r) et
              (posIterValid P b c0 c1 mc0 wc stb t pos vp)

-- the state of the run at stage i
stateAt : (P : Formula) (v0 : Val) -> Run P v0 -> Nat -> Val
stateAt P v0 (mkRun b c0 c1 mc0 wc stb mbc cyc rest mv0 wr) i =
  posState (posIter c0 c1 i (prod v0 rest))
