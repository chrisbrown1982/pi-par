module Main2

import public Data.Fin
import public Data.List
import public Data.Vect

public export
const2 : a -> b -> a 
const2 x = \y => x 

-------------------------------------------------------------------------------
-- Channels
public export
data Loc : Nat -> Type where
  Here  : Loc Z
  There : Loc n -> Loc (S n)

public export 
data InChan : Nat -> Type where
  MkIn : {n : Nat} -> Loc n -> InChan n

public export
data OutChan : Nat -> Type where
  MkOut : {n : Nat} -> Loc n -> OutChan n

public export 
data InChanTy : Nat -> List Type -> Type where
  MkInChanTy : (ch : Nat) -> (ts : List Type) -> InChanTy ch ts

public export
data OutChanTy : Nat -> List Type -> Type where
  MkOutChanTy : (ch : Nat) -> (ts : List Type) -> OutChanTy ch ts

public export
data StChanTy : Type where
  SendTy : List Type -> StChanTy
  RecvTy : List Type -> StChanTy

-------------------------------------------------------------------------------
-- State Definition & Management Operations

-- Type representing the state of the process in terms of channels.
-- A Process is either active or halted.
-- A halted process cannot be restarted.
-- An active process manages its set of live channels.
public export
data State : Nat -> Nat -> Type where
  Live : {n,m : Nat}
      -> (chs : Vect n StChanTy)
      -> (scs : Vect m Nat)
      -> State n m 
 -- End  : State Z Z
  -- Option: transition to End only permitted when all Channels are spent

public export
stIdxMsgTyOut' : {n : Nat} -> (chs : Vect n StChanTy) -> (ch  : Nat) -> Type
stIdxMsgTyOut' [] ch = Void
stIdxMsgTyOut' (SendTy [] :: chs) Z = Void
stIdxMsgTyOut' (SendTy (t :: ts) :: chs) Z = t
stIdxMsgTyOut' (RecvTy _  :: chs) Z = Void
stIdxMsgTyOut' (hd        :: chs) (S ch) = stIdxMsgTyOut' chs ch

public export
stIdxMsgTyOut : {m,n : Nat}
             -> (scs : Vect m Nat)
             -> (chs : Vect n StChanTy)
             -> (ch  : Nat)
             -> Type
stIdxMsgTyOut scs chs ch = case stIdxMsgTyOut' chs ch of
  InChanTy i ts => if elem i scs then InChanTy i ts else Void
  OutChanTy i ts => if elem i scs then OutChanTy i ts else Void
  t => t

public export
stIdxMsgTyIn : {n : Nat} -> (chs : Vect n StChanTy) -> (ch,i : Nat) -> Type
stIdxMsgTyIn [] ch i = Void
stIdxMsgTyIn (SendTy _  :: chs) Z i = Void
stIdxMsgTyIn (RecvTy [] :: chs) Z i = Void
stIdxMsgTyIn (RecvTy (InChanTy _ ss :: ts) :: chs) Z i = InChan i
stIdxMsgTyIn (RecvTy (OutChanTy _ ss :: ts) :: chs) Z i = OutChan i
stIdxMsgTyIn (RecvTy (t :: ts) :: chs) Z i = t
stIdxMsgTyIn (hd        :: chs) (S ch) i = stIdxMsgTyIn chs ch i

public export
stIdxMsgTyInRaw : {n : Nat} -> (chs : Vect n StChanTy) -> (ch : Nat) -> Type
stIdxMsgTyInRaw [] ch = Void
stIdxMsgTyInRaw (SendTy _  :: chs) Z = Void
stIdxMsgTyInRaw (RecvTy [] :: chs) Z = Void
stIdxMsgTyInRaw (RecvTy (t :: ts) :: chs) Z = t
stIdxMsgTyInRaw (hd        :: chs) (S ch) = stIdxMsgTyInRaw chs ch

public export
tail' : List a -> List a
tail' [] = []
tail' (x :: xs) = xs

public export
stDecAt : {n : Nat} -> (chs : Vect n StChanTy) -> (ch : Nat) -> Vect n StChanTy
stDecAt [] ch = [] -- no change
stDecAt (SendTy ts :: chs) Z = SendTy (tail' ts) :: chs
stDecAt (RecvTy ts :: chs) Z = RecvTy (tail' ts) :: chs
stDecAt (ch :: chs) (S k) = ch :: stDecAt chs k

public export
stEmptyAt : {n : Nat}
         -> (chs : Vect n StChanTy)
         -> (ch : Nat)
         -> Vect n StChanTy
stEmptyAt [] ch = []
stEmptyAt (SendTy ts :: chs) Z = SendTy [] :: chs
stEmptyAt (RecvTy ts :: chs) Z = RecvTy [] :: chs
stEmptyAt (ch :: chs) (S k) = ch :: stEmptyAt chs k

-- ...this is map.
public export
stApplyAt : (f   : List Type -> List Type)
         -> (chs : Vect n StChanTy)
         -> (ch  : Nat)
         -> Vect n StChanTy
stApplyAt f [] ch = []
stApplyAt f (SendTy ts :: chs) Z = SendTy (f ts) :: chs
stApplyAt f (RecvTy ts :: chs) Z = RecvTy (f ts) :: chs
stApplyAt f (ch :: chs) (S k) = ch :: stApplyAt f chs k

public export
stOutChBTy' : {n : Nat}
           -> (chs : Vect n StChanTy)
           -> (i,ch : Nat)
           -> Type
stOutChBTy' [] i ch = Void -- invalid channel
stOutChBTy' (RecvTy ts :: chs) Z ch = Void -- wrong direction
stOutChBTy' (SendTy [] :: chs) Z ch = Void -- nothing to delegate
stOutChBTy' (SendTy (t :: ts) :: chs) Z ch = OutChanTy ch (t :: ts)
stOutChBTy' (_ :: chs) (S k) ch = stOutChBTy' chs k ch

public export
stOutChBTy : {n : Nat}
          -> (chs : Vect n StChanTy)
          -> (i : Nat)
          -> Type
stOutChBTy chs i = stOutChBTy' chs i i

public export
stInChBTy' : {n : Nat}
          -> (chs : Vect n StChanTy)
          -> (i : Nat)
          -> (ch : Nat)
          -> Type
stInChBTy' [] i ch = Void -- invalid channel
stInChBTy' (RecvTy [] :: chs) Z ch = Void -- nothing to delegate
stInChBTy' (RecvTy (t :: ts) :: chs) Z ch = InChanTy ch (t :: ts)
stInChBTy' (SendTy ts :: chs) Z ch = Void
stInChBTy' (_ :: chs) (S k) ch = stInChBTy' chs k ch

public export
stInChBTy : {n : Nat}
         -> (chs : Vect n StChanTy)
         -> (i : Nat)
         -> Type
stInChBTy chs ch = stInChBTy' chs ch ch

-------------------------------------------------------------------------------
-- State Transition Functions
public export
SpawnSF : {t : Type}
       -> {n,m : Nat}
       -> (to,frm : List Type)
       -> (chs    : Vect n StChanTy)
       -> (scs    : Vect m Nat)
    --    -> (s0 : State n m)
       -> (x : t)
       -> State (plus n 2) m
SpawnSF to frm chs scs _ = Live (chs ++ [SendTy to, RecvTy frm]) scs

plusTwoSucc : (x : Nat) ->  S (S x) = plus x 2 

plusAssoc2 : (x: Nat) -> (y : Nat) -> (z : Nat) 
          -> plus x (plus y z) = plus (plus x y) z

public export
-- %inline %tcinline
SpawnSFN : {t : Type}
        -> {nChs,m : Nat}
        -> (num : Nat)
        -> (to,frm : List Type)
        -> (chs    : Vect nChs StChanTy)
        -> (scs    : Vect m Nat)
        -> (x : t)
        -> State (plus nChs (mult num 2)) m
SpawnSFN {nChs} Z to frm chs scs x = rewrite plusZeroRightNeutral nChs in Live chs scs
SpawnSFN {nChs} (S n) to frm chs scs x =
   let ret = SpawnSFN n to frm chs scs x 
        in case ret of 
                Live chs' scs' => 
                  let c = chs' ++ [SendTy to, RecvTy frm] 
                  in Live {n=plus nChs (mult (S n) 2)} (rewrite plusTwoSucc (mult n 2) 
                   in (rewrite plusAssoc2 nChs (mult n 2) 2 in c)) scs' -- Live c scs' --Live (chs' ++ [SendTy to, RecvTy frm]) scs'
               -- End => ?j
                -- End => ?hl2
--- try manually concat+replicate?
---    Live (chs ++ (concat (replicate (S n) 
---                                   [SendTy to, RecvTy frm]))) scs

-- SpanSFM : {t : Type}
--         -> {nChs,m : Nat}
--         -> (num : Nat)
--         -> (to,frm : List Type)
--         -> (chs    : Vect nChs StChanTy)
--         -> (scs    : Vect m Nat)
--         -> (t -> State n' m')
-- SpawnSFM Z = const st
-- SpawnSFM (S n) = SpawnSF (SpawnSFM n)

-- do Spawn ... -- SF 
--     Spawn ... -- SF SF x
--     Spawn ... -- SF SF SF x


{-
public export
SpawnSFN2 : {t : Type}
        -> {nChs,m : Nat}
        --- > (num : Nat)
        -> (to,frm : List Type)
        -> (chs    : Vect nChs StChanTy)
        -> (scs    : Vect m Nat)
        -> (x : t)
        -> State
-- SpawnSFN2 Z to frm chs scs = \_ => Live chs scs
SpawnSFN2 {nChs} to frm chs scs =
  \x => Live {n=plus nChs 2} (chs ++ [SendTy to, RecvTy frm]) scs


public export
serialSF : {t : Type}
        -> {n,m : Nat}
        -> (ch : Nat)
        -> (chs : Vect n StChanTy)
        -> (scs : Vect m Nat)
        -> (x : t)
        -> State
serialSF {t = Void} ch chs scs x with (x)
  serialSF {t = Void} ch chs scs x | p impossible
serialSF {t} ch chs scs x =
  Live (stApplyAt (const []) chs ch) (ch :: scs)

public export
sendSF : {t : Type}
      -> {n,m : Nat}
      -> (ch  : Nat)
      -> (chs : Vect n StChanTy)
      -> (scs : Vect m Nat)
      -> (msgTy : Type)
      -> (msg : msgTy)
      -> (x : t)
      -> State
sendSF ch chs scs Void msg x with (msg)
  sendSF ch chs scs Void msg x | p impossible
sendSF ch chs scs (InChanTy i ts) msg x =
  Live (stDecAt chs ch) (snd (delete i scs))
sendSF ch chs scs (OutChanTy i ts) msg x =
  Live (stDecAt chs ch) (snd (delete i scs))
sendSF ch chs scs msgTy msg x =
  Live (stDecAt chs ch) scs

public export
recvSF : {t : Type}
      -> {n,m : Nat}
      -> (ch : Nat)
      -> (chs : Vect n StChanTy)
      -> (scs : Vect m Nat)
      -> (ty : Type)
      -> (x : t)
      -> State
recvSF {t = Void} ch chs scs ty x with (x)
  recvSF {t = Void} ch chs scs ty x | p impossible
recvSF {t} ch chs scs (OutChanTy i ts) x =
  Live ((stDecAt chs ch) ++ [(SendTy ts)]) scs
recvSF {t} ch chs scs (InChanTy i ts) x =
  Live ((stDecAt chs ch) ++ [(RecvTy ts)]) scs
recvSF {t} ch chs scs ty x =
  Live (stDecAt chs ch) scs
-}
-------------------------------------------------------------------------------
-- Monad/State Machine Definition

public export
Spawned : {m : (ty : Type) -> (st : State (S (S Z)) Z) -> (ty -> State Z Z) -> Type}
       -> (inTy  : List Type)
       -> (outTy : List Type)
       -> Type
Spawned {m} inTy outTy =
  m () (Live [(RecvTy inTy), (SendTy outTy)] []) (const (Live [] []))

public export
data ProcessM : (ty : Type) -> (st : State n m) -> (ty -> State p m) -> Type where
  -- DSL operations
  Spawn : {chs : Vect n StChanTy}
       -> {scs : Vect m Nat}
       -> (to  : List Type)
       -> (frm : List Type)
       -> (p   : (pIn  : InChan  Z)      -- channel position in the child
              -> (pOut : OutChan (S Z))  
              -> Spawned {m = ProcessM} to frm)
       -> ProcessM (OutChan n, InChan (S n))
                   (Live chs scs)
                   (SpawnSF to frm chs scs)

  Halt  : ProcessM () (Live chs scs) (const (Live [] []))
  -- Standard operations
  Pure  : (x : t) -> ProcessM t st (const2 st)

--   Pure2 :  (t : Type)
--         -> (x : t)
--         -> (n : Nat)
--         -> (m : Nat)
--         -> (add : Nat)
--         -> (st : State n m) 
--         -> (st2 : State (n + add) m)
--   --     -> (r : StateR st st2)
--         ->  ProcessM t st (const2 st2)


  Pure2 : (x : t) -> ProcessM t (stFn x) stFn

  (>>=) : ProcessM a (Live chs scs) sf  
       -> ((x : a) -> ProcessM b (sf x) s3f)
       -> ProcessM b (Live chs scs) s3f
  (>>)  : ProcessM () (Live chs scs) sf
       -> ProcessM b (sf ()) s3f
       -> ProcessM b (Live chs scs) s3f

public export
Process : Type
Process = ProcessM () (Live [] []) (const (Live [] []))

------


data PM : (ty : Type) -> (st : State n m) -> (State p m) -> Type where
    -- Spawn : PM ty st (st ++ 2)
    Pure3 : PM ty st st
    Bind1 : PM a st st' -> (a -> PM b st' st'') -> PM b st st''

-------------------------------------------------------------------------------
-- Example

{-
calc : Process
calc =
  do
    (toP,frmP) <- Spawn [Nat, Nat] [Nat] [Nat, Nat] [Nat] p
    (toQ,frmQ) <- Spawn [OutChanTy [Nat]] [] [OutChanTy [Nat]] [] q
    Send toP Z
    -- Send toQ  -- (MkOutChan toP (Just (\ts => (take 1 ts, drop 1 ts))))
    ?after
    -- Halt
  where
    p : (pIn  : InChan  Z)
     -> (pOut : OutChan (S Z))
     -> Spawned {m = ProcessM} [Nat, Nat] [Nat]
    p pIn pOut = do
      x <- Recv pIn
      -- x <- Recv (MkIn (There Here))
      ?afterP
      -- Halt

    q : (qIn  : InChan  Z)
     -> (qOut : OutChan (S Z))
     -> Spawned {m = ProcessM} [OutChanTy [Nat]] []
    q qIn qOut = do
      toP <- Recv qIn
      Send toP Z
      ?afterQ
      -- Halt
-}

{-
test : Process
test =
  do
    -- (toP,frmP) <- Spawn [Nat] [InChanTy 6 [Nat]] p
    -- (toQ,frmQ) <- Spawn [InChanTy 6 [Nat]] [] q
    -- (toW,frmW) <- Spawn [InChanTy 6 [Nat]] [] w
    (toP,frmP) <- Spawn [Nat] [OutChanTy 6 [Nat]] p
    (toQ,frmQ) <- Spawn [OutChanTy 6 [Nat]] [] q
    (toW,frmW) <- Spawn [OutChanTy 6 [Nat]] [] w
    ch <- Recv frmP
    chS <- SOutC ch
    -- chS' <- SOutC ch
    Send toQ chS
    -- Send toW chS
    ?after
  where
    p pIn pOut = Halt
    q qIn qOut = Halt
    -- r rIn rOut = Halt
    w wIn wOut = Halt
-}

-------------------------------------------------------------------------------

{-
  main = do
    (to, frm) <- spawn [Nat, Nat] [Nat] p
    send to 1
    send to 2
    ans <- recv frm
    halt
-}

