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

data Chan : Type where
  MkInChan  : {n : Nat} -> InChan n  -> Chan
  MkOutChan : {n : Nat}
           -> OutChan n
           -- (ts -> (relinquishing, retaining))
           -> Maybe (List Type -> (List Type, List Type))
           -> Chan

fromChan : Chan -> Nat
fromChan (MkInChan {n} _) = n
fromChan (MkOutChan {n} _ _) = n

data ChanTy : Type where
  SendTy : List Type -> ChanTy
  RecvTy : List Type -> ChanTy

-------------------------------------------------------------------------------
-- State Definition & Management Operations

-- Type representing the state of the process in terms of channels.
-- A Process is either active or halted.
-- A halted process cannot be restarted.
-- An active process manages its set of live channels.
data State : Type where
  Live : {n : Nat} -> (chs : Vect n ChanTy) -> State
  End  : State
  -- Option: transition to End only permitted when all Channels are spent

stIdxMsgTyOut : {n : Nat} -> (chs : Vect n ChanTy) -> (ch  : Nat) -> Type
stIdxMsgTyOut [] ch = Void
stIdxMsgTyOut (SendTy [] :: chs) Z = Void
stIdxMsgTyOut (SendTy (t :: ts) :: chs) Z = t -- FIXME: what if Chan?
stIdxMsgTyOut (RecvTy _  :: chs) Z = Void
stIdxMsgTyOut (hd        :: chs) (S ch) = stIdxMsgTyOut chs ch

tail' : List a -> List a
tail' [] = []
tail' (x :: xs) = xs

stDecAt : {n : Nat} -> (chs : Vect n ChanTy) -> (ch : Nat) -> Vect n ChanTy
stDecAt [] ch = [] -- no change
stDecAt (SendTy ts :: chs) Z = SendTy (tail' ts) :: chs
stDecAt (RecvTy ts :: chs) Z = RecvTy (tail' ts) :: chs
stDecAt (ch :: chs) (S k) = ch :: stDecAt chs k

stEmptyAt : {n : Nat} -> (chs : Vect n ChanTy) -> (ch : Nat) -> Vect n ChanTy
stEmptyAt [] ch = []
stEmptyAt (SendTy ts :: chs) Z = SendTy [] :: chs
stEmptyAt (RecvTy ts :: chs) Z = RecvTy [] :: chs
stEmptyAt (ch :: chs) (S k) = ch :: stEmptyAt chs k

-- ...this is map.
stApplyAt : (f   : List Type -> List Type)
         -> (chs : Vect n ChanTy)
         -> (ch  : Nat)
         -> Vect n ChanTy
stApplyAt f [] ch = []
stApplyAt f (SendTy ts :: chs) Z = SendTy (f ts) :: chs
stApplyAt f (RecvTy ts :: chs) Z = RecvTy (f ts) :: chs
stApplyAt f (ch :: chs) (S k) = ch :: stApplyAt f chs k

stSplitAt : {n : Nat} -> (chs : Vect n ChanTy) -> (ch : Chan) -> Vect n ChanTy
stSplitAt chs (MkInChan {n} _) = stEmptyAt chs n
stSplitAt chs (MkOutChan {n} _ Nothing) = stEmptyAt chs n
stSplitAt chs (MkOutChan {n} _ (Just f)) = stApplyAt (snd . f) chs n

-------------------------------------------------------------------------------
-- State Transition Functions

spawnSF : {t : Type}
       -> {n : Nat}
       -> (to,frm : List Type)
       -> (chs    : Vect n ChanTy)
       -> (x : t)
       -> State
spawnSF to frm chs _ = Live (chs ++ [SendTy to, RecvTy frm])

sendSF : {t : Type}
      -> {n : Nat}
      -> (ch  : Nat)
      -> (chs : Vect n ChanTy)
      -> (msgTy : Type)
      -> (msg : msgTy)
      -> (x : t)
      -> State
sendSF ch chs Void msg x with (msg)
  sendSF ch chs Void msg x | p impossible
sendSF ch chs Chan msg x = Live (stSplitAt (stDecAt chs ch) msg)
sendSF ch chs msgTy msg x = Live (stDecAt chs ch)

-------------------------------------------------------------------------------
-- Monad/State Machine Definition

Spawned : {m : (ty : Type) -> (st : State) -> (ty -> State) -> Type}
       -> (inTy  : List Type)
       -> (outTy : List Type)
       -> Type
Spawned {m} inTy outTy =
  m () (Live [(RecvTy inTy), (SendTy outTy)]) (const End)

data ProcessM : (ty : Type) -> (st : State) -> (ty -> State) -> Type where
  -- DSL operations
  Spawn : {chs : Vect n ChanTy}   
       -> (to  : List Type)
       -> (frm : List Type)
       -> (p   : (pIn  : InChan  Z)
              -> (pOut : OutChan (S Z))
              -> Spawned {m = ProcessM} frm to)
       -> ProcessM (OutChan n, InChan (S n))
                   (Live chs)
                   (spawnSF to frm chs)
  Send  : {chs : Vect n ChanTy}
       -> {m   : Nat}
       -> (ch  : OutChan m)
       -> (msg : stIdxMsgTyOut chs m)
       -> ProcessM () (Live chs) (sendSF m chs (stIdxMsgTyOut chs m) msg)
  Halt  : ProcessM () (Live chs) (const End)
  -- Standard operations
  Pure  : (x : t) -> ProcessM t st (const st)
  (>>=) : ProcessM a (Live chs) sf 
       -> ((x : a) -> ProcessM b (sf x) s3f)
       -> ProcessM b (Live chs) s3f
  (>>)  : ProcessM () (Live chs) sf
       -> ProcessM b (sf ()) s3f
       -> ProcessM b (Live chs) s3f

Process : Type
Process = ProcessM () (Live []) (const End)

-------------------------------------------------------------------------------
-- Example

calc : Process
calc =
  do
    (toP,frmP) <- Spawn [Nat, Nat, Nat, Nat] [Nat] p
    (toQ,frmQ) <- Spawn [Chan] [] q
    Send toP Z
    Send toQ (MkOutChan toP (Just (\ts => (take 1 ts, drop 1 ts))))
    ?after
    -- Halt
  where
    p frm to = Halt
    q frm to = Halt

-------------------------------------------------------------------------------

{-
  main = do
    (to, frm) <- spawn [Nat, Nat] [Nat] p
    send to 1
    send to 2
    ans <- recv frm
    halt
-}

