module Main4

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
data ChanLin : Type where
    Active : ChanLin
    Serial : ChanLin
    Spent  : ChanLin

public export
data StChanTy : Type where
  SendTy : List Type -> ChanLin -> StChanTy
  RecvTy : List Type -> ChanLin -> StChanTy

-------------------------------------------------------------------------------
-- State Definition & Management Operations

-- Type representing the state of the process in terms of channels.
-- A Process is either active or halted.
-- A halted process cannot be restarted.
-- An active process manages its set of live channels.
public export
data State : Type where
  Live : {n : Nat}
      -> (chs : Vect n StChanTy)
      -> State
  End  : State
  -- Option: transition to End only permitted when all Channels are spent

public export
stIdxMsgTyOut' : {n : Nat} -> (chs : Vect n StChanTy) -> (ch  : Nat) -> Type
stIdxMsgTyOut' [] ch = Void
stIdxMsgTyOut' (SendTy [] _ :: chs) Z = Void
stIdxMsgTyOut' (SendTy (t :: ts) Active :: chs) Z = t
stIdxMsgTyOut' (SendTy (t :: ts) _ :: chs) Z = Void
stIdxMsgTyOut' (RecvTy _ _ :: chs) Z = Void
stIdxMsgTyOut' (hd        :: chs) (S ch) = stIdxMsgTyOut' chs ch

public export
tail' : List a -> List a
tail' [] = []
tail' (x :: xs) = xs

public export
stDecAt : {n : Nat} -> (chs : Vect n StChanTy) -> (ch : Nat) -> Vect n StChanTy
stDecAt [] ch = [] -- no change
stDecAt (SendTy [] l :: chs) Z = SendTy [] l :: chs
stDecAt (SendTy (t :: ts) l :: chs) Z = SendTy ts l :: chs
stDecAt (RecvTy ts l :: chs) Z = RecvTy (tail' ts) l :: chs
stDecAt (ch :: chs) (S k) = ch :: stDecAt chs k


public export
sendSF : {n   : Nat}
      -> (ch  : Nat)
      -> (chs : Vect n StChanTy)
    --   -> (msgTy : Type)
    --   -> (msg : msgTy)
      -> State
sendSF ch chs =
  Live (stDecAt chs ch)

public export
data ProcessM : (ty : Type) -> (st : State) -> State -> Type where

  Halt  : ProcessM () (Live chs) End
  -- Standard operations
  Pure  : (x : t) -> ProcessM t st st

  (>>=) : ProcessM a (Live chs) st2  
       -> ((x : a) -> ProcessM b st2 st3)
       -> ProcessM b (Live chs) st3
  (>>)  : ProcessM () (Live chs) st2
       -> ProcessM b st2 st3
       -> ProcessM b (Live chs) st3

  Send  : {chs : Vect n StChanTy}
       -> {m   : Nat}
       -> (ch  : OutChan m)
       -> (msg : stIdxMsgTyOut' chs m)
       -> ProcessM
            ()
            (Live chs)
            (sendSF m chs)

up : {k : Nat}
  -> {chs : Vect k StChanTy}
  -> (n : Nat)
  -> (chsS  : (Vect len (m : Nat ** (OutChan m, stIdxMsgTyOut' chs m))))
  -> Vect len (m : Nat ** (OutChan m, stIdxMsgTyOut' (stDecAt chs n) m))
up n [] = []
up n ((m ** (o, msg)) :: css) = (m ** (o, ?d)) :: up n css

public export 
sendSFN :
         {n, len : Nat}
      -> (chs : Vect n StChanTy)
      -> (chsS  : (Vect len (m : Nat ** (OutChan m, stIdxMsgTyOut' chs m))))
      -> State
sendSFN chs [] = Live chs
sendSFN chs ((m ** (out, msg))::chss)
  = sendSFN (stDecAt chs m) (up m chss)  


public export
sendN  : {n : Nat}
      -> {chs : Vect n StChanTy}
      -> (chsS  : (Vect len (m : Nat ** (OutChan m, stIdxMsgTyOut' chs m))))
      -> ProcessM
           ()
           (Live chs)
           (sendSFN chs chsS)
sendN [] = Pure ()
sendN ((m ** (c, msg))  ::cs) = 
    do  -- sendN cs
        Send c msg
        sendN (up m cs)