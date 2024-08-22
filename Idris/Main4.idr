module Main4

import public Data.Fin
import public Data.List
import public Data.Vect
import public Decidable.Equality

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




-------------------------------------------------------------------------------
-- State Transition Functions
public export
spawnSF : -- {t : Type}
          {n : Nat}
       -> (toT,frmT : Type)
       -> (chs    : Vect n (t ** (StChanTy t)))
       -> State
spawnSF toT frmT chs = Live (chs ++ [(toT ** SendTy toT), (frmT ** RecvTy frmT)])

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

  Spawn : {chs : Vect n StChanTy}
    -> (to  : Type)
    -> (frm : Type)
    -> (p   : (pIn  : InChan  Z)      -- channel position in the child
           -> (pOut : OutChan (S Z))  
           -> Spawned {m = ProcessM} to frm)
    -> ProcessM (OutChan n, InChan (S n))
                (Live chs)
                (spawnSF to frm chs)


  Send  : {chs : Vect n StChanTy}
       -> {m   : Nat}
       -> (ch  : OutChan m)
       -> (msg : stIdxMsgTyOut' chs m)
       -> ProcessM
            ()
            (Live chs)
            (sendSF m chs)

data ChVect : (len : Nat) -> (m : Nat) -> (chs : Vect k StChanTy) -> Type where 
       ChNil  : ChVect 0 m [] 
       ChCons : {m : Nat}
             -> (o : OutChan (m+1)) 
             -> (t : stIdxMsgTyOut' chs (m+1)) 
             -> (tail : ChVect len m chs)
             -> (prf : Not (m = (m+1))) 
             -> ChVect (len + 1) (m+1) chs

up : {k : Nat}
  -> {chs : Vect k StChanTy}
  -> (n : Nat)
  -> (chsS  : (Vect len (m : Nat ** (OutChan m, stIdxMsgTyOut' chs m))))
  -> Vect len (m : Nat ** (OutChan m, stIdxMsgTyOut' (stDecAt chs n) m))
up n [] = []
up n ((m ** (o, msg)) :: css) = (m ** (o, ?d)) :: up n css

voidElim : Void -> a 
voidElim v impossible

lem1: (n : Nat) -> (m : Nat) -> (p : Not (n = m)) -> (stIdxMsgTyOut' (stDecAt chs n) m  = stIdxMsgTyOut' chs m)

{-
stIdxMsgTyOut' : {n : Nat} -> (chs : Vect n StChanTy) -> (ch  : Nat) -> Type
stIdxMsgTyOut' [] ch = Void
stIdxMsgTyOut' (SendTy [] _ :: chs) Z = Void
stIdxMsgTyOut' (SendTy (t :: ts) Active :: chs) Z = t
stIdxMsgTyOut' (SendTy (t :: ts) _ :: chs) Z = Void
stIdxMsgTyOut' (RecvTy _ _ :: chs) Z = Void
stIdxMsgTyOut' (hd        :: chs) (S ch) = stIdxMsgTyOut' chs ch
-}

lem2' : (c : StChanTy) -> (cs : Vect k StChanTy) -> (m : Nat) -> (p2 : NonZero m) -> stIdxMsgTyOut' (c :: cs) m 
                       ->  stIdxMsgTyOut' cs m
lem2' c cs (S m') p2 msgT = ?o1

lem2'' :  (c : StChanTy) -> stIdxMsgTyOut' (stDecAt cs (S x)) m ->  stIdxMsgTyOut' (stDecAt (c::cs) (S x)) m

public export
lem2 : {k : Nat} -> (n : Nat) -> (m : Nat) -> (chs : Vect k StChanTy)
    -> (p2 : NonZero n) 
    -> (msgT : stIdxMsgTyOut' chs m) -> stIdxMsgTyOut' (stDecAt chs n) m
lem2 (S x) m [] SIsNonZero msgT = msgT
lem2 (S x) m (c :: cs) SIsNonZero msgT = let ind = lem2 (S x) m cs SIsNonZero (lem2' c cs m ?p5 msgT) in lem2'' c ind

up2 : {k : Nat}
-> {chs : Vect k StChanTy}
-> (n : Nat) -- channel we have just sent on
-> (chsS  : (ChVect len m chs)) -- the remainder of the channels that we have yet to send
-> ChVect len m (stDecAt chs n) -- the remainder updated (which shouldn't do anything)
up2 n ChNil = ?h2
up2 n (ChCons {m} o msgT css prf) = let msgT' = lem2 n (m + 1) chs ?p msgT 
                                        in ChCons o msgT' (up2 n css) prf  -- (m ** (o, ?d)) :: up n css

public export 
sendSFN :
         {n, len : Nat}
      -> (chs : Vect n StChanTy) -- initial state
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