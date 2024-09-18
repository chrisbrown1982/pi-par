module ParLib

import public Data.List
import public Data.Vect

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
data StChanTy : (t : Type) -> Type where
  SendTy : (t : Type) -> StChanTy t
  RecvTy : (t : Type) -> StChanTy t

-------------------------------------------------------------------------------
-- State

public export
data State : Type where
  Live : {n : Nat} -> (chs : Vect n (t ** StChanTy t)) -> State
  End  : State

-------------------------------------------------------------------------------
-- State Transition Functions

public export
spawnSF : {n : Nat}
       -> (toT,frmT : Type)
       -> (chs    : Vect n (t ** (StChanTy t)))
       -> State
spawnSF toT frmT chs =
  Live (chs ++ [(toT ** SendTy toT), (frmT ** RecvTy frmT)])

-------------------------------------------------------------------------------
-- Process Monad

public export
Spawned : {m : (ty : Type) -> (st : State) -> State -> Type}
       -> (inTy  : Type)
       -> (outTy : Type)
       -> Type
Spawned {m} inTy outTy =
  m () (Live [(inTy ** RecvTy inTy), (outTy ** SendTy outTy)]) End

public export
data ProcessM : (ty : Type) -> (st : State) -> State -> Type where
  Spawn : {chs : Vect n (t ** StChanTy t)}
       -> (to  : Type)
       -> (frm : Type)
       -> (p   : (pIn  : InChan  Z)
              -> (pOut : OutChan (S Z))  
              -> Spawned {m = ProcessM} to frm)
       -> ProcessM (OutChan n, InChan (S n))
                   (Live chs)
                   (spawnSF to frm chs)


  Halt   : ProcessM () (Live chs) End
  Return : (x : t) -> ProcessM t (Live chs) End

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
      -> (ty : Type)
      -> (ch  : InChan m)
      -> ProcessM
          (ty)
          (Live chs)
          (Live chs)

  -- Standard operations
  Pure  : (x : t) -> ProcessM t st st
  (>>=) : ProcessM a (Live chs) st2  
       -> ((x : a) -> ProcessM b st2 st3)
       -> ProcessM b (Live chs) st3
  (>>)  : ProcessM () (Live chs) st2
       -> ProcessM b st2 st3
       -> ProcessM b (Live chs) st3

public export
Process : Type
Process = ProcessM () (Live []) End

public export 
fChan : (a, b) -> a 

public export
sChan : (a, b) -> b

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

