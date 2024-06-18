module Main

import Data.Fin
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

chToNat : {m : Nat} -> (chTy : Nat -> Type) -> chTy m -> Nat
chToNat {m} _ _ = m

-------------------------------------------------------------------------------
-- State Definition & Management Operations

-- Environment item type
-- Nº Tokens, Message Type
record Chan where
  constructor MkChan
  bound     : Nat
  msgType   : Type

-- Type representing the state of the process in terms of channels.
-- A Process is either active or halted.
-- A halted process cannot be restarted.
-- An active process manages its set of live channels.
data State : Type where
  Live : {n : Nat} -> (chs : Vect n Chan) -> State
  End  : State
  -- Option: transition to End only permitted when all Channels are spent

empty : State
empty = Live []

stIdxMsgTy' : {n : Nat} -> (chs : Vect n Chan) -> (ch  : Nat) -> Type
stIdxMsgTy' [] ch = Void -- can't send on an unregistered channel
stIdxMsgTy' (MkChan Z _ :: _) Z = Void -- can't send on a spent channel
stIdxMsgTy' (ch :: _) Z = msgType ch
stIdxMsgTy' (_ :: chs) (S ch) = stIdxMsgTy' chs ch

stIdxMsgTy : {m, n : Nat}
          -> (chTy : Nat -> Type)
          -> (chs : Vect n Chan)
          -> (ch : chTy m)
          -> Type
stIdxMsgTy chTy chs ch = stIdxMsgTy' chs (chToNat chTy ch)

stIdxMsgTyS' : {n : Nat} -> (chs : Vect n Chan) -> (ch  : Nat) -> Maybe Type
stIdxMsgTyS' [] ch = Nothing
stIdxMsgTyS' (MkChan Z _ :: _) Z = Nothing
stIdxMsgTyS' (ch :: _) Z = Just (msgType ch)
stIdxMsgTyS' (_ :: chs) (S ch) = stIdxMsgTyS' chs ch

stIdxMsgTyS : {m, n : Nat}
           -> (chTy : Nat -> Type)
           -> (chs : Vect n Chan)
           -> (ch : chTy m)
           -> Maybe Type
stIdxMsgTyS chTy chs ch = stIdxMsgTyS' chs (chToNat chTy ch)

stDecAt : {n : Nat} -> (chs : Vect n Chan) -> (ch : Nat) -> Vect n Chan
stDecAt [] ch = [] -- no change
stDecAt (MkChan b t :: chs) Z = MkChan (pred b) t :: chs
stDecAt (ch :: chs) (S k) = ch :: stDecAt chs k

-------------------------------------------------------------------------------
-- State Transition Functions

spawnSF : {n : Nat}
       -> (outB,  inB  : Nat)
       -> (outTy, inTy : Type)
       -> (chs         : Vect n Chan)
       -> (x : t)
       -> State
spawnSF outB inB outTy inTy chs x =
  Live (chs ++ [(MkChan outB outTy), (MkChan inB inTy)])

decSF : {m,n  : Nat}
     -> (chTy : Nat -> Type)
     -> (chs  : Vect n Chan)
     -> (ch   : chTy m)
     -> (x : t)
     -> State
decSF {m} _ chs _ _ = Live (stDecAt chs m)

recvSF : {t : Type}
      -> {m,n : Nat}
      -> (chs : Vect n Chan)
      -> (ch  : InChan m)
      -> (x : t)
      -> State
recvSF {t = Void} chs ch x with (x)
  recvSF {t = Void} chs ch x | _ impossible
recvSF {t = t} chs ch x = decSF InChan chs ch x

-------------------------------------------------------------------------------
-- Monad/State Machine Definition

data SpawnedP : Type where
  TODO_SpawnedP : SpawnedP

data ProcessM : (ty : Type) -> (st : State) -> (ty -> State) -> Type where
  -- DSL operations
  Spawn : {chs  : Vect b Chan}
       -> (outB : Nat) -> (outTy : Type)
       -> (inB  : Nat) -> (inTy : Type)
       -> (p    : SpawnedP)
       -> ProcessM (OutChan b, InChan (S b))
                   (Live chs)
                   (spawnSF outB inB outTy inTy chs)
  Send  : {chs : Vect ub Chan}
       -> (ch  : OutChan m)
       -> (msg : stIdxMsgTy OutChan chs ch)
       -> ProcessM () (Live chs) (decSF OutChan chs ch)
  Recv  : {chs : Vect ub Chan}
       -> (ch  : InChan m)
       -> ProcessM (stIdxMsgTy InChan chs ch) (Live chs) (recvSF chs ch)
  Halt   : ProcessM () (Live chs) (const End)

  -- Standard operations
  Pure   : (x : t) -> ProcessM t st (const st)
  (>>=)  : ProcessM a (Live chs) sf 
        -> ((x : a) -> ProcessM b (sf x) s3f)
        -> ProcessM b (Live chs) s3f
  (>>)   : ProcessM () (Live chs) sf
        -> ProcessM b (sf ()) s3f
        -> ProcessM b (Live chs) s3f

Process : Type
Process = ProcessM () empty (const End)

spawn : {chs : Vect b Chan}
     -> (to, frm : (Nat, Type)) -> (p : SpawnedP)
     -> ProcessM (OutChan b, InChan (S b))
                 (Live chs)
                 (spawnSF (fst to) (fst frm) (snd to) (snd frm) chs)
spawn (toB,toTy) (frmB,frmTy) p = Spawn toB toTy frmB frmTy p

send : {chs : Vect b Chan}
    -> (ch  : OutChan m)
    -> (msg : stIdxMsgTy OutChan chs ch)
    -> ProcessM () (Live chs) (decSF OutChan chs ch)
send = Send

recv : {m,n : Nat}
    -> {chs : Vect n Chan}
    -> (ch  : InChan m)
    -> ProcessM (stIdxMsgTy InChan chs ch) (Live chs) (recvSF chs ch)
recv = Recv

-------------------------------------------------------------------------------
-- Example

test : Process
test = do
  (to, frm) <- spawn (2,Nat) (1,Nat) TODO_SpawnedP
  send to 1
  send to 1
  let x = MkIn (There (There Here))
  ans <- recv frm
  Halt

-------------------------------------------------------------------------------

{-
  main = do                             []
    (to, frm) <- spawn 2 Nat 1 Nat p    [(Out, 2, Nat),(In, 1, Nat)]
    send to 1                           [(Out, 1, Nat),(In, 1, Nat)]
    send to 1                           [(Out, 0, Nat),(In, 1, Nat)]
    ans <- recv fm                      [(Out, 0, Nat),(In, 0, Nat)]
-}

{-
  [Done] 1. Tidy up & fix Recv
  2. Delegation primitives
  3. Deal with Proc
  4. Skeleton example & usage
  5. Translate

-}
