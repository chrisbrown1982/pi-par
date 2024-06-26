module New

import Data.Fin
import Data.List
import Data.Vect

-------------------------------------------------------------------------------
-- Channels

data Loc : Nat -> Type where
  Here  : Loc Z
  There : Loc n -> Loc (S n)

data InChan : Nat -> Type where
  MkIn : {n : Nat} -> Loc n -> InChan n

data OutChan : Nat -> Type where
  MkOut : {n : Nat} -> Loc n -> OutChan n

data InChanTy : Nat -> List Type -> Type where
  MkInChanTy : (ch : Nat) -> (ts : List Type) -> InChanTy ch ts
data OutChanTy : Nat -> List Type -> Type where
  MkOutChanTy : (ch : Nat) -> (ts : List Type) -> OutChanTy ch ts

data StChanTy : Type where
  SendTy : List Type -> StChanTy
  RecvTy : List Type -> StChanTy

-------------------------------------------------------------------------------
-- State Definition & Management Operations

-- Type representing the state of the process in terms of channels.
-- A Process is either active or halted.
-- A halted process cannot be restarted.
-- An active process manages its set of live channels.
data State : Type where
  Live : {n,m : Nat}
      -> (chs : Vect n StChanTy)
      -> (scs : Vect m Nat)
      -> State
  End  : State
  -- Option: transition to End only permitted when all Channels are spent

stIdxMsgTyOut' : {n : Nat} -> (chs : Vect n StChanTy) -> (ch  : Nat) -> Type
stIdxMsgTyOut' [] ch = Void
stIdxMsgTyOut' (SendTy [] :: chs) Z = Void
stIdxMsgTyOut' (SendTy (t :: ts) :: chs) Z = t
stIdxMsgTyOut' (RecvTy _  :: chs) Z = Void
stIdxMsgTyOut' (hd        :: chs) (S ch) = stIdxMsgTyOut' chs ch

stIdxMsgTyOut : {m,n : Nat}
             -> (scs : Vect m Nat)
             -> (chs : Vect n StChanTy)
             -> (ch  : Nat)
             -> Type
stIdxMsgTyOut scs chs ch = case stIdxMsgTyOut' chs ch of
  InChanTy i ts => if elem i scs then InChanTy i ts else Void
  OutChanTy i ts => if elem i scs then OutChanTy i ts else Void
  t => t


stIdxMsgTyIn : {n : Nat} -> (chs : Vect n StChanTy) -> (ch,i : Nat) -> Type
stIdxMsgTyIn [] ch i = Void
stIdxMsgTyIn (SendTy _  :: chs) Z i = Void
stIdxMsgTyIn (RecvTy [] :: chs) Z i = Void
stIdxMsgTyIn (RecvTy (InChanTy _ ss :: ts) :: chs) Z i = InChan i
stIdxMsgTyIn (RecvTy (OutChanTy _ ss :: ts) :: chs) Z i = OutChan i
stIdxMsgTyIn (RecvTy (t :: ts) :: chs) Z i = t
stIdxMsgTyIn (hd        :: chs) (S ch) i = stIdxMsgTyIn chs ch i

stIdxMsgTyInRaw : {n : Nat} -> (chs : Vect n StChanTy) -> (ch : Nat) -> Type
stIdxMsgTyInRaw [] ch = Void
stIdxMsgTyInRaw (SendTy _  :: chs) Z = Void
stIdxMsgTyInRaw (RecvTy [] :: chs) Z = Void
stIdxMsgTyInRaw (RecvTy (t :: ts) :: chs) Z = t
stIdxMsgTyInRaw (hd        :: chs) (S ch) = stIdxMsgTyInRaw chs ch

tail' : List a -> List a
tail' [] = []
tail' (x :: xs) = xs

stDecAt : {n : Nat} -> (chs : Vect n StChanTy) -> (ch : Nat) -> Vect n StChanTy
stDecAt [] ch = [] -- no change
stDecAt (SendTy ts :: chs) Z = SendTy (tail' ts) :: chs
stDecAt (RecvTy ts :: chs) Z = RecvTy (tail' ts) :: chs
stDecAt (ch :: chs) (S k) = ch :: stDecAt chs k

stEmptyAt : {n : Nat}
         -> (chs : Vect n StChanTy)
         -> (ch : Nat)
         -> Vect n StChanTy
stEmptyAt [] ch = []
stEmptyAt (SendTy ts :: chs) Z = SendTy [] :: chs
stEmptyAt (RecvTy ts :: chs) Z = RecvTy [] :: chs
stEmptyAt (ch :: chs) (S k) = ch :: stEmptyAt chs k

-- ...this is map.
stApplyAt : (f   : List Type -> List Type)
         -> (chs : Vect n StChanTy)
         -> (ch  : Nat)
         -> Vect n StChanTy
stApplyAt f [] ch = []
stApplyAt f (SendTy ts :: chs) Z = SendTy (f ts) :: chs
stApplyAt f (RecvTy ts :: chs) Z = RecvTy (f ts) :: chs
stApplyAt f (ch :: chs) (S k) = ch :: stApplyAt f chs k

stOutChBTy' : {n : Nat}
           -> (f : List Type -> (List Type, List Type))
           -> (chs : Vect n StChanTy)
           -> (i,ch,n0 : Nat)
           -> Type
stOutChBTy' f [] i ch n0 = Void -- invalid channel
stOutChBTy' f (RecvTy ts :: chs) Z ch n0 = Void -- wrong direction
stOutChBTy' f (SendTy [] :: chs) Z ch n0 = Void -- nothing to delegate
stOutChBTy' f (SendTy (t :: ts) :: chs) Z ch n0 =
  case f (t :: ts) of
    (xs,[]) => OutChanTy ch xs
    (xs,(y :: ys)) => (OutChanTy ch xs, OutChan n0)
stOutChBTy' f (_ :: chs) (S k) ch n0 = stOutChBTy' f chs k ch n0

stOutChBTy : {n : Nat}
          -> (f : List Type -> (List Type, List Type))
          -> (chs : Vect n StChanTy)
          -> (i : Nat)
          -> Type
stOutChBTy {n} f chs i = stOutChBTy' f chs i i n

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

stInChBTy : {n : Nat}
         -> (chs : Vect n StChanTy)
         -> (i : Nat)
         -> Type
stInChBTy chs ch = stInChBTy' chs ch ch

stShiftLen : {n : Nat}
          -> (chs : Vect n StChanTy)
          -> (ch  : Nat) 
          -> Nat
stShiftLen [] ch = Z
stShiftLen ((::) {len} ch chs) Z = S (len + 1)
stShiftLen (ch :: chs) (S k) = S (stShiftLen chs k)

stShiftAt : {n : Nat}
         -> (f : List Type -> List Type)
         -> (chs : Vect n StChanTy)
         -> (ch  : Nat)
         -> Vect (stShiftLen chs ch) StChanTy
stShiftAt f [] ch = []
stShiftAt f ((::) {len} (SendTy ts) chs) Z =
  SendTy [] :: chs ++ [SendTy (f ts)]
stShiftAt f ((::) {len} (RecvTy ts) chs) Z =
  RecvTy [] :: chs ++ [RecvTy (f ts)]
stShiftAt f (ch :: chs) (S k) = ch :: stShiftAt f chs k

-------------------------------------------------------------------------------
-- State Transition Functions

spawnSF : {t : Type}
       -> {n,m : Nat}
       -> (to,frm : List Type)
       -> (chs    : Vect n StChanTy)
       -> (scs    : Vect m Nat)
       -> (x : t)
       -> State
spawnSF to frm chs scs _ = Live (chs ++ [SendTy to, RecvTy frm]) scs

serialSF : {t : Type}
        -> {n,m : Nat}
        -> (f : List Type -> (List Type, List Type))
        -> (ch : Nat)
        -> (chs : Vect n StChanTy)
        -> (scs : Vect m Nat)
        -> (x : t)
        -> State
serialSF {t = Void} f ch chs scs x with (x)
  serialSF {t = Void} f ch chs scs x | p impossible
serialSF {t = (r,s)} f ch chs scs x =
  Live (stShiftAt (snd . f) chs ch) (ch :: scs)
serialSF {t} f ch chs scs x =
  Live (stApplyAt (snd . f) chs ch) (ch :: scs)

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

-------------------------------------------------------------------------------
-- Monad/State Machine Definition

Spawned : {m : (ty : Type) -> (st : State) -> (ty -> State) -> Type}
       -> (inTy  : List Type)
       -> (outTy : List Type)
       -> Type
Spawned {m} inTy outTy =
  m () (Live [(RecvTy inTy), (SendTy outTy)] []) (const End)

data ProcessM : (ty : Type) -> (st : State) -> (ty -> State) -> Type where
  -- DSL operations
  Spawn : {chs : Vect n StChanTy}
       -> {scs : Vect m Nat}
       -> (to  : List Type)
       -> (frm : List Type)
       -> (p   : (pIn  : InChan  Z)
              -> (pOut : OutChan (S Z))
              -> Spawned {m = ProcessM} to frm)
       -> ProcessM (OutChan n, InChan (S n))
                   (Live chs scs)
                   (spawnSF to frm chs scs)
  SOutC : {chs : Vect n StChanTy}
       -> {scs : Vect k Nat}
       -> (ch : OutChan m)
       -> (f  : List Type -> (List Type, List Type))
                          -- (relinquishing, retaining)
                          -- FIXME
       -> ProcessM (stOutChBTy f chs m) -- if partial, return new channel
                   (Live chs scs)
                   (serialSF f m chs scs)
  SInC  : {chs : Vect n StChanTy}
       -> {scs : Vect k Nat}
       -> (ch  : InChan m)
       -> ProcessM (stInChBTy chs m)
                   (Live chs scs)
                   (serialSF (\ts => (ts,[])) m chs scs)
  Send  : {chs : Vect n StChanTy}
       -> {scs : Vect k Nat}
       -> {m   : Nat}
       -> (ch  : OutChan m)
       -> (msg : stIdxMsgTyOut scs chs m)
       -> ProcessM
            ()
            (Live chs scs)
            (sendSF m chs scs (stIdxMsgTyOut scs chs m) msg)
  Recv  : {chs : Vect n StChanTy}
       -> {scs : Vect k Nat}
       -> {m   : Nat}
       -> (ch  : InChan m)
       -> ProcessM
            (stIdxMsgTyIn chs m n)
            (Live chs scs)
            (recvSF m chs scs (stIdxMsgTyInRaw chs m))
  Halt  : ProcessM () (Live chs scs) (const End)
  -- Standard operations
  Pure  : (x : t) -> ProcessM t st (const st)
  (>>=) : ProcessM a (Live chs scs) sf 
       -> ((x : a) -> ProcessM b (sf x) s3f)
       -> ProcessM b (Live chs scs) s3f
  (>>)  : ProcessM () (Live chs scs) sf
       -> ProcessM b (sf ()) s3f
       -> ProcessM b (Live chs scs) s3f

Process : Type
Process = ProcessM () (Live [] []) (const End)

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

test : Process
test =
  do
    -- (toP,frmP) <- Spawn [Nat] [InChanTy 6 [Nat]] p
    -- (toQ,frmQ) <- Spawn [InChanTy 6 [Nat]] [] q
    -- (toW,frmW) <- Spawn [InChanTy 6 [Nat]] [] w
    (toP,frmP) <- Spawn [Nat] [OutChanTy 6 [Nat,Nat]] p
    (toQ,frmQ) <- Spawn [OutChanTy 6 [Nat]] [] q
    (toW,frmW) <- Spawn [OutChanTy 6 [Nat]] [] w
    ch <- Recv frmP
    -- ch' <- SOutC (MkOut (There Here)) (\ts => (ts,[]))
    (chS, ch') <- SOutC ch (\ts => (take 1 ts, drop 1 ts))
    -- chS' <- SOutC ch (\ts => (ts,[]))
    -- chS' <- SOutC ch' (\ts => (ts,[]))
    Send toQ chS
    -- Send toW chS

    -- (toR,frmR) <- Spawn [] [] r
    -- x <- Recv frmR
    -- Send toP 42
    ?after

    -- ch2' <- SOutC ch (\ts => (ts,[]))
    -- ch' <- SInC ch
    -- ch2' <- SInC ch
    -- Send toQ ch'
    -- Send toW ch'
    -- ?after
    -- Halt
  where
    p pIn pOut = Halt
    q qIn qOut = Halt
    -- r rIn rOut = Halt
    w wIn wOut = Halt

-------------------------------------------------------------------------------

{-
  main = do
    (to, frm) <- spawn [Nat, Nat] [Nat] p
    send to 1
    send to 2
    ans <- recv frm
    halt
-}

