{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Walk -- finite ->-paths, materialised as lists.
--
-- LTL.Gfp already has Path, which is what Reach_U(v) is in m4.tex section 3;
-- that is the right form for gfpSound and gfpComplete, where nothing is ever
-- built.  Phase 6 builds: a round is a path, a lasso is two paths, and the
-- evaluation of G25 indexes into them.  So the same relation is given again
-- carrying the list of states it visits, and indexed by its endpoint:
--
--   Walk P us v ws x   --  v -> ws_1 -> ... -> ws_n = x, every ws_i in us
--
-- Indexing by the endpoint rather than computing it with a "last" function is
-- what keeps the concatenations below free of equational bookkeeping.
--
-- The one substantial lemma is walkPersist: along a walk, an eventuality
-- pending at the start is either fulfilled at a state visited, or still pending
-- at the endpoint.  That is Lemma 2.8 of the note (persistence, discharged in
-- LTL.Step as `persist`) propagated along a path, and it is what both the round
-- construction (G22) and the cycle-fulfilment property (G23) turn on.

module LTL.Walk where

open import LTL.Trace public

------------------------------------------------------------------------
-- Walks

data Walk (P : Formula) (us : List Val) : Val -> List Val -> Val -> Set where
  wnil  : {v : Val} -> Walk P us v [] v
  wcons : {v w : Val} {ws : List Val} {x : Val}
       -> Mem w us -> Eq (step P v w) true
       -> Walk P us w ws x -> Walk P us v (w :: ws) x

walkApp : (P : Formula) (us : List Val) {v x y : Val} {ws zs : List Val}
       -> Walk P us v ws x -> Walk P us x zs y -> Walk P us v (append ws zs) y
walkApp P us wnil             w2 = w2
walkApp P us (wcons mw st w1) w2 = wcons mw st (walkApp P us w1 w2)

-- The endpoint is one of the states visited.
walkEnd : (P : Formula) (us : List Val) {v : Val} {ws : List Val} {x : Val}
       -> Walk P us v ws x -> Mem x (v :: ws)
walkEnd P us wnil             = memHd
walkEnd P us (wcons mw st wk) = memTl (walkEnd P us wk)

-- Every state a walk visits after its start lies in us.
walkIn : (P : Formula) (us : List Val) {v : Val} {ws : List Val} {x : Val}
      -> Walk P us v ws x -> {z : Val} -> Mem z ws -> Mem z us
walkIn P us wnil             ()
walkIn P us (wcons mw st wk) memHd     = mw
walkIn P us (wcons mw st wk) (memTl m) = walkIn P us wk m

------------------------------------------------------------------------
-- Membership under concatenation

memConsApp : {z v : Val} (ws zs : List Val)
          -> Mem z (v :: ws) -> Mem z (v :: append ws zs)
memConsApp ws zs memHd     = memHd
memConsApp ws zs (memTl m) = memTl (memAppL ws zs m)

-- A state visited by the second leg is visited by the concatenation, given
-- that the joint x is visited by the first.
memConsApp2 : {z v x : Val} (ws zs : List Val)
           -> Mem x (v :: ws) -> Mem z (x :: zs) -> Mem z (v :: append ws zs)
memConsApp2 ws zs mx memHd     = memConsApp ws zs mx
memConsApp2 ws zs mx (memTl m) = memTl (memAppR ws zs m)

nullB_appR : (ws : List Val) (y : Val) (zs : List Val)
          -> Eq (nullB (append ws (y :: zs))) false
nullB_appR []        y zs = refl
nullB_appR (w :: ws) y zs = refl

nullB_appL : (ws zs : List Val)
          -> Eq (nullB ws) false -> Eq (nullB (append ws zs)) false
nullB_appL []        zs ()
nullB_appL (w :: ws) zs e = refl

------------------------------------------------------------------------
-- The tail of a walk starting at any state it visits.
--
-- Needed for the cycle-fulfilment property: "travelling along the cycle from
-- s" of the proof of Proposition 5.3.

data SubWalk (P : Formula) (us : List Val) (s x v : Val) (ws : List Val) : Set where
  subWalk : (zs : List Val) -> Walk P us s zs x
         -> ({z : Val} -> Mem z (s :: zs) -> Mem z (v :: ws))
         -> SubWalk P us s x v ws

subWalkTl : {P : Formula} {us : List Val} {s x v w : Val} {ws : List Val}
         -> SubWalk P us s x w ws -> SubWalk P us s x v (w :: ws)
subWalkTl (subWalk zs wz f) = subWalk zs wz (\ m -> memTl (f m))

walkFrom : (P : Formula) (us : List Val) {v : Val} {ws : List Val} {x : Val}
        -> Walk P us v ws x -> {s : Val} -> Mem s (v :: ws) -> SubWalk P us s x v ws
walkFrom P us wnil             memHd     = subWalk [] wnil (\ m -> m)
walkFrom P us wnil             (memTl ())
walkFrom P us (wcons mw st wk) memHd     =
  subWalk _ (wcons mw st wk) (\ m -> m)
walkFrom P us (wcons mw st wk) (memTl m) = subWalkTl (walkFrom P us wk m)

------------------------------------------------------------------------
-- Fulfilment along a walk

data Fulfil (P : Formula) (A : Formula) (v : Val) (ws : List Val) : Set where
  ful : (z : Val) -> Mem z (v :: ws) -> Eq (valOf P z A) false -> Fulfil P A v ws

fulTl : {P A : Formula} {v w : Val} {ws : List Val}
     -> Fulfil P A w ws -> Fulfil P A v (w :: ws)
fulTl (ful z m q) = ful z (memTl m) q

fulApp : {P A : Formula} {v : Val} (ws zs : List Val)
      -> Fulfil P A v ws -> Fulfil P A v (append ws zs)
fulApp ws zs (ful z m q) = ful z (memConsApp ws zs m) q

fulApp2 : {P A : Formula} {v x : Val} (ws zs : List Val)
       -> Mem x (v :: ws) -> Fulfil P A x zs -> Fulfil P A v (append ws zs)
fulApp2 ws zs mx (ful z m q) = ful z (memConsApp2 ws zs mx m) q

------------------------------------------------------------------------
-- Persistence along a walk (Lemma 2.8, propagated).
--
-- If box A is pending at v then, walking to x, either A fails somewhere along
-- the way -- the eventuality is fulfilled -- or box A is still pending at x.
-- The step is exactly `persist`: box A pending at v together with A holding at
-- v forces box A pending at the successor, which is (T3).

walkPersist : (P : Formula) (us : List Val) (A : Formula) -> Mem (box A) (sub P)
           -> {v : Val} {ws : List Val} {x : Val} -> Walk P us v ws x
           -> Eq (valOf P v (box A)) false
           -> Sum (Fulfil P A v ws) (Eq (valOf P x (box A)) false)
walkPersist P us A mb wnil e = inr e
walkPersist P us A mb (wcons {v} {w} {ws} {x} mw st wk) e = onA (valOf P v A) refl
  where
    onA : (b : Bool) -> Eq (valOf P v A) b
       -> Sum (Fulfil P A v (w :: ws)) (Eq (valOf P x (box A)) false)
    onA false ea = inl (ful v memHd ea)
    onA true  ea =
      sumElim (\ f -> inl (fulTl f)) inr
              (walkPersist P us A mb wk (persist P v w A mb st e ea))
