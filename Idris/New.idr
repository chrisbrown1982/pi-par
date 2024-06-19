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

-------------------------------------------------------------------------------
-- Message Type NF

{-
  NB: Would need reflection to ensure that 'Chan', 'InChan', 'OutChan' aren't
  subexpressions of any of the ground types. Any channels smuggled in 
  groundOpts will simply not be delegated.
-}

data MsgTy : Type where
  MkMTy : {n,m : Nat}
       -> (base : Vect m Type)
       -> (chs  : Vect n Chan)
       -> MsgTy

-------------------------------------------------------------------------------
-- State Definition & Management Operations

-- Environment item type
-- Direction, Nº Tokens, Message Type
record SChan where
  constructor MkSChan
  direction : Dir
  bound     : Nat
  msgType   : Type

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

-------------------------------------------------------------------------------
-- Monad/State Machine Definition

data ChanDef : Type where
  MkDef : (bound : Nat) -> (msgTy : MsgTy) -> ChanDef

Spawned : {m : (ty : Type) -> (st : State) -> (ty -> State) -> Type}
       -> {outB,inB : Nat}
       -> (outbox : OutChan outB)
       -> (inbox  : InChan inB)
       -> Type
Spawned {m} {outB} {inB} _ _ =
  m () (Live [MkSChan Out Z Nat, MkSChan In Z Nat]) (const End)

data ProcessM : (ty : Type) -> (st : State) -> (ty -> State) -> Type where
  -- DSL operations
  Spawn : {chs : Vect n SChan}
       --  -> (to  : ChanDef)
       --  -> (frm : ChanDef)
       -> (p   : (to  : OutChan Z)
              -> (frm : InChan (S Z))
              -> Spawned {m = ProcessM} to frm)
       -> ProcessM (OutChan n, InChan (S n))
                   (Live chs)
                   (const (Live chs))
 
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
  let pTo = MkDef 3 (MkMTy [Ping] [])
  in do
    x <- Spawn (\to, frm => Halt)
    ?after
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
