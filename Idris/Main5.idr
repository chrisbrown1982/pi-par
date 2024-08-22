module Main5 

import public Data.Fin
import public Data.List
import public Data.Vect
import public Decidable.Equality


{-
public export
data ChanLin : Type where
    Active : ChanLin
    Serial : ChanLin
    Spent  : ChanLin
-}

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
data InChanTy : Nat -> Type -> Type where
  MkInChanTy : (ch : Nat) -> (t : Type) -> InChanTy ch t

public export
data OutChanTy : Nat -> Type -> Type where
  MkOutChanTy : (ch : Nat) -> (t : Type) -> OutChanTy ch t

public export
data StChanTy : (t : Type) -> Type where
  SendTy : (t : Type) -> StChanTy t
  RecvTy : (t : Type) -> StChanTy t

public export
data State : Type where
    Live : {n : Nat}
        -> (chs : Vect n (t ** StChanTy t))
        -> State
    End  : State


public export
stIdxMsgTyIn : {n : Nat} -> (chs : Vect n (t ** StChanTy t)) -> (ch,i : Nat) -> Type
stIdxMsgTyIn [] ch i = Void
stIdxMsgTyIn ((t ** SendTy _)  :: chs) Z i = Void
stIdxMsgTyIn ((t ** RecvTy t) :: chs) Z i = t
-- stIdxMsgTyIn ((t ** RecvTy (InChanTy _ ss :: ts)) :: chs) Z i = InChan i
-- stIdxMsgTyIn ((t ** RecvTy (OutChanTy _ ss :: ts)) :: chs) Z i = OutChan i
-- stIdxMsgTyIn ((t ** RecvTy (t :: ts)) :: chs) Z i = t
stIdxMsgTyIn (hd        :: chs) (S ch) i = stIdxMsgTyIn chs ch i 

public export
stIdxMsgTyInRaw : {n : Nat} -> (chs : Vect n (t ** StChanTy t)) -> (ch : Nat) -> Type
stIdxMsgTyInRaw [] ch = Void
stIdxMsgTyInRaw ((t ** SendTy _)  :: chs) Z = Void
stIdxMsgTyInRaw ((t ** RecvTy t) :: chs) Z = t
stIdxMsgTyInRaw (hd        :: chs) (S ch) = stIdxMsgTyInRaw chs ch

public export
Spawned : {m : (ty : Type) -> (st : State) -> State -> Type}
       -> (inTy  : Type)
       -> (outTy : Type)
       -> Type
Spawned {m} inTy outTy =
  m () (Live [(inTy ** RecvTy inTy), (outTy ** SendTy outTy)]) End


public export
recvSF : 
         {n : Nat}
      -> (ch : Nat)
      -> (chs : Vect n (t ** StChanTy t))
      -> (ty : Type)
      -> State
recvSF ch chs (OutChanTy i t) =
  Live (chs ++ [(t ** SendTy t)])
recvSF ch chs (InChanTy i t) =
  Live (chs ++ [(t ** RecvTy t)])
recvSF ch chs ty =
  Live chs

public export
recvSFN : 
           {n : Nat}
        -> (m : Nat)
        -> (chs : Vect n (t ** StChanTy t))
        -> (tys : Type)
        -> State
recvSFN Z chs t = Live chs
recvSFN (S k) chs (OutChanTy i t) =
    recvSFN k (chs ++ [(t ** SendTy t)]) t
recvSFN (S k) chs (InChanTy i t) =
    recvSFN k (chs ++ [(t ** RecvTy t)]) t
recvSFN (S k) chs t = recvSFN k chs t

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


  Spawn : {chs : Vect n (t ** StChanTy t)}
    -> (to  : Type)
    -> (frm : Type)
    -> (p   : (pIn  : InChan  Z)      -- channel position in the child
           -> (pOut : OutChan (S Z))  
           -> Spawned {m = ProcessM} to frm)
    -> ProcessM (OutChan n, InChan (S n))
                (Live chs)
                (spawnSF to frm chs)

  Send  : {chs : (Vect n (t ** StChanTy t))}
       -> {m   : Nat}
       -> (ch  : OutChan m)
       -> (msg : t)
       -> ProcessM
            ()
            (Live chs)
            (Live chs)

  Recv : {chs : Vect n (t ** StChanTy t)}
      -> {m   : Nat}
      -> (ch  : InChan m)
      -> ProcessM
          (stIdxMsgTyIn chs m n)
          (Live chs)
          (recvSF m chs (stIdxMsgTyInRaw chs m))

public export
SpawnSFN : -- {t : Type}
            {nChs : Nat}
         -> (num : Nat)
         -> (chs : (Vect nChs (t ** StChanTy t)))
         -> (toT, frmT : Type)
         -> State
SpawnSFN Z chs toT frmT = Live chs
SpawnSFN (S n) chs toT frmT = 
     SpawnSFN n (chs ++ [(toT ** (SendTy toT)), (frmT ** (RecvTy frmT))]) toT frmT

public export
SpawnN : {n : Nat}
      -> {chs : Vect n (t ** StChanTy t)}
      -> (num : Nat)
      -> (toTy : Type)
      -> (frmTy : Type)
      -> (p  : (pIn  : InChan  Z)
            -> (pOut : OutChan (S Z))
            -> Spawned {m = ProcessM} toTy frmTy)
      -> ProcessM
            (List (m ** (OutChan m, InChan (S m))))
            (Live chs)
            (SpawnSFN num chs toTy frmTy)
SpawnN {n} Z toTy frmTy p = Pure []
SpawnN {n} (S num) toTy frmTy p = 
  do
    s <- Spawn toTy frmTy p 
    r <- SpawnN num toTy frmTy p 
    Pure ((n ** s) :: r)


public export
SendN  : {n : Nat}
      -> {chs : Vect n (t ** StChanTy t)}
      -> (msgs  : (Vect len (m : Nat ** (t : Type ** (OutChan m, t)))))
      -> ProcessM
           ()
           (Live chs)
           (Live chs)
SendN [] = Pure () 
SendN ((m ** (t ** (c, msg))) :: cs) = 
    do Send c msg 
       SendN cs
       Pure () 

{-
  Recv : {chs : Vect n (t ** StChanTy t)}
      -> {m   : Nat}
      -> (ch  : InChan m)
      -> ProcessM
          (stIdxMsgTyIn chs m n)
          (Live chs)
          (recvSF m chs (stIdxMsgTyInRaw chs m))
-}

public export
RecN : {m : Nat} 
    -> {chs : Vect n (t ** StChanTy t)}
    -> (msgTy : Type)
    -> (inChs : List (InChan m))
    -> ProcessM 
            (List msgTy)
            (Live chs) 
            (recvSFN m chs msgTy)
RecN msgTy [] = ?h1
RecN msgTy (c :: chs) = 
    do -- m <- Recv c
       msgs <- RecN msgTy chs
       ?h
