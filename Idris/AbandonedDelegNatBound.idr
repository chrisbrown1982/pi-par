module New

import Data.Vect

-------------------------------------------------------------------------------
-- Channels

data Dir : Type where
  In  : Dir
  Out : Dir

data Loc : Nat -> Type where
  Here  : Loc Z
  There : Loc n -> Loc (S n)

data InChan : Nat -> Type where
  MkIn : {n : Nat} -> Loc n -> InChan n

data OutChan : Nat -> Type where
  MkOut : {n : Nat} -> Loc n -> OutChan n

data ChanF : Nat -> Type where
  IsIn  : {n : Nat} -> InChan n -> ChanF n
  IsOut : {n : Nat} -> OutChan n -> ChanF n

data Chan : Type where -- to avoid dependent pairs in MsgTy
  MkChan : {n : Nat} -> ChanF n -> Chan

data ChanDef : Type where
  MkDef : (bound  : Nat)
       -> (msgTy  : Type)
       -> (getChs : msgTy -> Maybe Chan)
       -> ChanDef

fromDir : Dir -> (Nat -> Type)
fromDir In  = InChan
fromDir Out = OutChan

chToNat : {m : Nat} -> (chTy : Nat -> Type) -> chTy m -> Nat
chToNat {m} _ _ = m

-------------------------------------------------------------------------------
-- State Definition & Management Operations

-- Environment item type
-- Direction, Nº Tokens, Message Type
record SChan where
  constructor MkSChan
  direction : Dir
  bound     : Nat
  msgType   : Type
  projChans : msgType -> Maybe Chan

-- Type representing the state of the process in terms of channels.
-- A Process is either active or halted.
-- A halted process cannot be restarted.
-- An active process manages its set of live channels.
data State : Type where
  Live : {n : Nat} -> (chs : Vect n SChan) -> State
  End  : State
  -- Option: transition to End only permitted when all Channels are spent

empty : State
empty = Live []

stIdxMsgTyIn : {n : Nat} -> (chs : Vect n SChan) -> (ch  : Nat) -> Type
stIdxMsgTyIn [] ch = Void -- can't recv on an unregistered channel
stIdxMsgTyIn (MkSChan _ Z _ _ :: _) Z = Void -- can't recv on a spent channel
stIdxMsgTyIn (MkSChan Out _ _ _ :: _) Z = Void -- can't recv on an output channel
stIdxMsgTyIn (ch :: _) Z = msgType ch
stIdxMsgTyIn (_ :: chs) (S ch) = stIdxMsgTyIn chs ch

stIdxMsgTyOut : {n : Nat} -> (chs : Vect n SChan) -> (ch  : Nat) -> Type
stIdxMsgTyOut [] ch = Void -- can't send on an unregistered channel
stIdxMsgTyOut (MkSChan _ Z _ _ :: _) Z = Void -- can't send on a spent channel
stIdxMsgTyOut (MkSChan In _ _ _ :: _) Z = Void -- can't send on an input channel
stIdxMsgTyOut (ch :: _) Z = msgType ch
stIdxMsgTyOut (_ :: chs) (S ch) = stIdxMsgTyOut chs ch

stIdxMsgTy : {n   : Nat}
          -> (dir : Dir)
          -> (chs : Vect n SChan)
          -> (ch  : Nat)
          -> Type
stIdxMsgTy In chs ch = stIdxMsgTyIn chs ch
stIdxMsgTy Out chs ch = stIdxMsgTyOut chs ch

stDecAt : {n : Nat} -> (chs : Vect n SChan) -> (ch : Nat) -> Vect n SChan
stDecAt [] ch = [] -- no change
stDecAt (MkSChan d b t f :: chs) Z = MkSChan d (pred b) t f :: chs
stDecAt (ch :: chs) (S k) = ch :: stDecAt chs k

-------------------------------------------------------------------------------
-- State Transition Functions

decSF : {n   : Nat}
     -> (chs : Vect n SChan)
     -> (ch  : Nat)
     -> (x : t)
     -> State
decSF chs ch _ = Live (stDecAt chs ch)

spawnSF : {t : Type}
       -> {n : Nat}
       -> (to,frm : ChanDef)
       -> (chs    : Vect n SChan)
       -> (x : t)
       -> State
spawnSF {t} (MkDef toB toT toF) (MkDef frmB frmT frmF) chs x =
  Live (chs ++ [(MkSChan Out toB toT toF), (MkSChan In frmB frmT frmF)])

sendSF : {t   : Type}
      -> {m,n : Nat}
      -> (fwd : Vect m SChan)
      -> (chs : Vect n SChan)
      -> (ch  : Nat)
      -> (msg : stIdxMsgTy Out chs ch)
      -> t
      -> State
sendSF chs [] ch msg x with (x)
  sendSF chs [] ch msg x | p impossible 
sendSF chs (MkSChan Out (S n) t f :: as) Z msg x = 
  case f msg of
    Nothing  => Live (chs ++ (MkSChan Out n t f :: as))
    Just ch  => ?todo
    -- if ch <= m then ch in m else
      -- if ch == (S m) then we're sending the ch we're sending on (allowed?)
      -- else ch in as
    -- update the ch entry by reducing it to nothing
    -- reconstruct chs, decrementing t
sendSF chs (MkSChan In n t f :: as) Z msg x = ?isimpossible
sendSF chs (a :: as) (S ch) msg x = sendSF (chs ++ [a]) as ch ?here x

-------------------------------------------------------------------------------
-- Monad/State Machine Definition

Spawned : {m : (ty : Type) -> (st : State) -> (ty -> State) -> Type}
       -> {outB,inB : Nat}
       -> (outbox : OutChan outB)
       -> (inbox  : InChan inB)
       -> Type
Spawned {m} {outB} {inB} _ _ =
  m () (Live [(MkSChan Out Z Nat ?h1), (MkSChan In Z Nat ?h2)]) (const End)

data ProcessM : (ty : Type) -> (st : State) -> (ty -> State) -> Type where
  -- DSL operations
  Spawn : {chs : Vect n SChan}
       -> (to  : ChanDef)
       -> (frm : ChanDef)
       -> (p   : (to  : OutChan Z)
              -> (frm : InChan (S Z))
              -> Spawned {m = ProcessM} to frm)
       -> ProcessM (OutChan n, InChan (S n))
                   (Live chs)
                   (spawnSF to frm chs)
  Send  : {chs : Vect n SChan}
       -> (ch  : OutChan m) 
       -> (msg : stIdxMsgTy Out chs (chToNat OutChan ch))
       -> ProcessM () (Live chs) (sendSF [] chs (chToNat OutChan ch) msg)
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
Process = ProcessM () empty (const End)

-------------------------------------------------------------------------------
-- Example

Ping : Type
Ping = ()
Pong : Type
Pong = ()

pingpongP : Process
pingpongP =
  do
    (pingTo, pingFrm) <- Spawn (MkDef 3 (Either Ping Chan) fP)
                               (MkDef 2 () (const Nothing))
                               (\to, frm => Halt)
    (pongTo, pongFrm) <- Spawn (MkDef 3 (Either Ping Chan) fP)
                               (MkDef 2 () (const Nothing))
                               (\to, frm => Halt)
    Send pingTo (Left ())
    Send pingTo (Right (MkChan (IsOut pingTo)))
    ?after
  where
    fP : Either Ping Chan -> Maybe Chan
    fP (Left _) = Nothing
    fP (Right ch) = Just ch
{-
  let pingCh = ChDef 3
  in do
    ?after

pingCh : ChanDef
pingCh = ChDef 3 Nat (\t => ?here)
-}

-------------------------------------------------------------------------------
-- Sketch

{-
pingP outbox inbox = do
  pongFrm <- recv inbox
  pongTo  <- recv inbox
  send pongTo Ping
  msg <- recv pongFrm
  halt

pongP outbox inbox = do
  pingFrm <- recv inbox
  pingTo  <- recv inbox
  msg <- recv pingFrm 
  send pingTo Pong
  halt

pingpong = do
  (pingTo, pingFrm) <- spawn pingP
  (pongTo, pongFrm) <- spawn pongP
  send pingTo pongFrm
  send pongTo pingFrm
  send pingTo pongTo
  send pongTo pingTo
  halt
-}
