module Main5 

import public Data.Fin
import public Data.List
import public Data.Vect
import public Decidable.Equality

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

  Ret  : (x : t) -> ProcessM t (Live chs) End

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
      -> (ty : Type)
      -> (ch  : InChan m)
      -> ProcessM
          (ty)
          (Live chs)
          (Live chs)



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
            (Vect num (m ** (OutChan m, InChan (S m))))
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

public export
RecN : {chs : Vect n (t ** StChanTy t)}
    -> (msgTy : Type)
    -> (inChs : Vect len (m : Nat ** InChan m))
    -> ProcessM 
            (List msgTy) -- (m ** stIdxMsgTyIn chs m n))
            (Live chs) 
            (Live chs)
RecN ty [] = Pure []
RecN ty ((m ** c) :: chs) = 
    do m1 <- Recv ty c
       msgs <- RecN ty chs
       Pure (m1 :: msgs)

public export
Process : Type
Process = ProcessM () (Live []) End

test : Process
test = 
    do 
        (to, frm) <- Spawn Nat Nat p
        Send to 42
        v <- Recv Nat frm
        Halt

 where
    p :  (pIn : InChan Z)
      -> (pOut : OutChan (S Z))
      -> Spawned {m = ProcessM} Nat Nat
    p pIn pOut = do
                    x <- Recv Nat pIn
                    Send pOut 42
                    Halt

convertChans : (t : Type) 
            -> Vect len (m : Nat ** (OutChan m, InChan (S m)))
            -> (msgs : Vect len t)
            -> Vect len (m : Nat ** (t : Type ** (OutChan m, t)))
convertChans t [] msgs = []
convertChans t ((m ** (o,i)) :: rest) (msg::msgs) = 
   (m ** (t ** (o, msg))) :: convertChans t rest msgs 

inChans : Vect len (m : Nat ** (OutChan m, InChan (S m))) -> Vect len (n : Nat ** InChan n)
inChans [] = []
inChans ((m ** (o, i))::chs) = ((S m) ** i) :: inChans chs


farm4 : (inTy : Type)
   ->  (outTy : Type)
  -- ->  (nW : Nat)
   ->  (w : (pIn : InChan Z)
         -> (pOut : OutChan (S Z))
         -> Spawned {m = ProcessM} inTy outTy)
   ->  (input : Vect 4 inTy)
   ->  ProcessM (List outTy) (Live []) End
farm4 inTy outTy w input = 
    do
        res <- SpawnN 4 inTy outTy w 

        SendN (convertChans inTy res input)

        msgs <- RecN outTy (inChans res)

        Ret msgs

        


farmTest : Process 
farmTest = 
    do 
       res <- SpawnN 4 Nat Nat w
       SendN (convertChans Nat res [1,2,3,4])
       msgs <- RecN Nat (inChans res)
       Halt
        
 where 
    w : (pIn : InChan cid)
          -> (pOut : OutChan (S cid))
          -> Spawned {m = ProcessM} Nat Nat
    w pIn pOut = do 
                    Halt 

    