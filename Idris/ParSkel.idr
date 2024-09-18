module ParSkel

import ParLib

import public Data.Fin
import public Data.List
import public Data.Vect
import public Decidable.Equality

data MsgT : Type where 
      End : MsgT 
      Msg : Nat -> MsgT


public export
spawnN : (n : Nat)
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
spawnN n Z toTy frmTy p = Pure []
spawnN n (S num) toTy frmTy p = 
  do
    s <- Spawn toTy frmTy p 
    r <- spawnN (n+2) num toTy frmTy p 
    Pure ((n ** s) :: r)



public export
sendN  : {n : Nat}
      -> {chs : Vect n (t ** StChanTy t)}
      -> (msgs  : (Vect len (m : Nat ** (t : Type ** (OutChan m, t)))))
      -> ProcessM
           ()
           (Live chs)
           (Live chs)
sendN [] = Pure () 
sendN ((m ** (t ** (c, msg))) :: cs) = 
    do Send c msg 
       sendN cs
       Pure () 

public export
roundRobin : 
      -- {len : Nat}
       {chs : Vect n (t ** StChanTy t)}
      -> (msgT : Type)
      -> (msgs: Vect msgLen msgT)
      -> (chs2 :  Vect len (m : Nat ** (OutChan m)))
      -> (chs3 : Vect len2 (m : Nat ** (OutChan m)))
      -> ProcessM 
            ()
            (Live chs)
            (Live chs)
roundRobin msgT [] x y = Pure ()
roundRobin msgT (ms::msgs) [] chs2 = roundRobin msgT (ms::msgs) chs2 chs2 
roundRobin msgT (ms::msgs) ((m ** c)::chs) chs2 = 
      do Send c ms 
         roundRobin msgT msgs chs chs2 
         Pure ()


public export
recN : {chs : Vect n (t ** StChanTy t)}
    -> (msgTy : Type)
    -> (inChs : Vect len (m : Nat ** InChan m))
    -> ProcessM 
            (List msgTy) -- (m ** stIdxMsgTyIn chs m n))
            (Live chs) 
            (Live chs)
recN ty [] = Pure []
recN ty ((m ** c) :: chs) = 
    do m1 <- Recv c
       msgs <- recN ty chs
       Pure (m1 :: msgs)


p :  (pIn : InChan Z)
      -> (pOut : OutChan (S Z))
      -> Spawned {m = ProcessM} Nat Nat
p pIn pOut = do
                    x <- Recv pIn
                    Send pOut 42
                    Halt

test : Process
test = 
    do 
        c <- Spawn Nat Nat p
        Send (fChan c) 42
        v <- Recv c
        Halt



convertChans : (t : Type) 
            -> Vect len (m : Nat ** (OutChan m, InChan (S m)))
            -> (msgs : Vect len t)
            -> Vect len (m : Nat ** (t : Type ** (OutChan m, t)))
convertChans t [] msgs = []
convertChans t ((m ** c) :: rest) (msg::msgs) = 
   (m ** (t ** (fChan c, msg))) :: convertChans t rest msgs 

convertChansRR : 
               Vect len (m : Nat ** (OutChan m, InChan (S m)))
            -> Vect len (m : Nat ** (OutChan m))
convertChansRR [] = []
convertChansRR ((m ** c) :: rest) = 
   (m ** (fChan c)) :: convertChansRR rest 

inChans : Vect len (m : Nat ** (OutChan m, InChan (S m))) -> Vect len (n : Nat ** InChan n)
inChans [] = []
inChans ((m ** i)::chs) = ((S m) ** sChan i) :: inChans chs


farm4 : (inTy : Type)
   ->  (outTy : Type)
   ->  (nW : Nat)
   ->  (w : (pIn : InChan Z)
         -> (pOut : OutChan (S Z))
         -> Spawned {m = ProcessM} inTy outTy)
   ->  (input : Vect 4 inTy)
   ->  ProcessM (List outTy) (Live []) End
farm4 inTy outTy nw w input = 
    do
        res <- spawnN 0 4 inTy outTy w
        sendN (convertChans inTy res input)
        msgs <- recN outTy (inChans res)
        Return msgs


pRR :  (pIn : InChan Z)
      -> (pOut : OutChan (S Z))
      -> Spawned {m = ProcessM} Nat Nat
pRR pIn pOut = do
                    x <- Recv pIn
                    Send pOut x
                    pRR pIn pOut 
                    Halt

farm4RR : (nW : MsgT)
   ->  (w : (pIn : InChan Z)
         -> (pOut : OutChan (S Z))
         -> Spawned {m = ProcessM} MsgT MsgT)
   ->  (input : Vect 4 MsgT)
   ->  ProcessM (List Nat) (Live []) End
farm4RR nw w input = 
    do
        res <- spawnN 0 4 MsgT MsgT pRR
        roundRobin MsgT input (convertChansRR res) (convertChansRR res)
        msgs <- recN MsgT (inChans res)
        Return msgs

{-
pipeTest : Process 
pipeTest = 
    do 
        (in1, out1) <- Spawn Nat Nat stage1 
        Send in1 42
        res <- Recv Nat out1 
        Halt 
 where 
    stage2 : (pIn : InChan Z) 
          -> (pOut : OutChan (S Z))
          -> Spawned {m = ProcessM} Nat Nat 
    stage2 pIn pOut = do
                         Send pOut 42
                         Halt


    stage1 : (pIn : InChan Z) 
          -> (pOut : OutChan (S Z))
          -> Spawned {m = ProcessM} Nat Nat 
    stage1 pIn pOut = do 
                            (stg2In, stgOut) <- Spawn Nat Nat stage2 
                            msg <- Recv Nat pIn  
                            Send stg2In msg
                            res <- Recv Nat stgOut 
                            Send pOut res 
                            Halt 

 
w : (pIn : InChan cid)
 -> (pOut : OutChan (S cid))
 -> Spawned {m = ProcessM} Nat Nat
w pIn pOut = do 
                Halt 

rem : Nat -> Nat -> Nat

gcd2 : Nat -> Nat -> Nat 
gcd2 a 0 = a 
gcd2 a b = gcd2 b (a `rem` b)



relPrime : Nat -> Nat -> Bool
relPrime x y = (gcd2 x y) == 1 


mkList : Nat -> List Nat 
mkList n = [1..n]


euler : Nat -> Nat 
euler n = 
    length ( filter (\x => relPrime n x) (mkList n))


sumEuler : Nat -> Nat 
sumEuler n = 
    sum ( map (\x => euler(x)) (mkList n))

farmTest : Process 
farmTest = 
    do 
       res <- spawnN 0 4 Nat Nat p
       sendN (convertChans Nat res [[1],[2],[3],[4]])
       msgs <- recN Nat (inChans res)
       Halt


-}
