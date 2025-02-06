module Farm 

import ParLib
import public Data.Fin
import public Data.List
import public Data.Vect
import public Decidable.Equality

data MsgT : Type where 
      MEnd : MsgT 
      Msg :  Nat -> MsgT


public export
spawnN : (n : Nat)
      -> (chs : Vect n (t ** StChanTy t))
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
spawnN Z [] Z toTy frmTy p = Pure [] -- Pure ?h1 -- []
spawnN (S n) (c::chs) Z toTy frmTy p = Pure [] -- Pure ?h1 -- []
spawnN Z [] (S num) toTy frmTy p = ?h1 
spawnN (S n) (c::chs) (S num) toTy frmTy p = 
  do
    (i,o) <- Spawn toTy frmTy p 
    --r <- spawnN (S (n+2)) (c::chs) num toTy frmTy p 
    ?h2
--    Pure ((n ** s) :: r)

{-
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
   --   -> (chs3 : Vect len2 (m : Nat ** (OutChan m)))
      -> ProcessM 
            ()
            (Live chs)
            (Live chs)
roundRobin msgT [] [] = Pure ()
roundRobin msgT [] ((m ** c)::chs) =
   do Send c MEnd 
      roundRobin msgT [] chs 
      Pure () 
roundRobin msgT (m :: ms) [] = Pure ()
roundRobin msgT (ms::msgs) ((m ** c)::chs) = 
    do Send c ms 
       roundRobin msgT msgs (chs ++ [(m**c)]) 
       Pure ()

public export
roundRobinRec : 
    {chs : Vect n (t ** StChanTy t)}
 -> (nMsgs : Nat)
 -> (chs2 :  Vect len (m : Nat ** (InChan m)))
 -> ProcessM 
      (List MsgT)
      (Live chs)
      (Live chs)
roundRobinRec Z x = Pure []
roundRobinRec (S n) [] = Pure []
roundRobinRec (S n) ((m ** c)::chs) = 
 do m1 <- Recv MsgT c 
    msgs <- roundRobinRec n (chs ++ [(m**c)])
    Pure (m1 :: msgs)

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
convertChansRR ((m ** c) :: rest) = (m ** (fChan c)) :: convertChansRR rest 

inChans : Vect len (m : Nat ** (OutChan m, InChan (S m))) -> Vect len (n : Nat ** InChan n)
inChans [] = []
inChans ((m ** i)::chs) = ((S m) ** sChan i) :: inChans chs

outChans : Vect len (m : Nat ** (OutChan m, InChan (S m))) -> Vect len (n : Nat ** OutChan n)
outChans [] = []
outChans ((m ** i)::chs) = (m ** fChan i) :: outChans chs

pRR :  (pIn : InChan Z)
    -> (pOut : OutChan (S Z))
    -> Spawned {m = ProcessM} MsgT MsgT
pRR pIn pOut = do
                  x <- Recv MsgT pIn
                  case x of 
                      MEnd => do -- Send pOut MEnd 
                                 Halt
                      Msg m => do Send pOut (Msg (m + 100))
                                  y <- pRR pIn pOut 
                                  Pure ()

farm4RR : (nW : MsgT)
   ->  (w : (pIn : InChan Z)
         -> (pOut : OutChan (S Z))
         -> Spawned {m = ProcessM} MsgT MsgT)
   ->  (input : Vect 4 MsgT)
   ->  ProcessM (List MsgT) (Live []) End
farm4RR nw w input = 
    do
        res <- spawnN 0 4 MsgT MsgT pRR
        roundRobin MsgT input (convertChansRR res) 
        msgs <- roundRobinRec (length input) (inChans res)
        Return msgs

farm4RR2 : (nW : Nat)
->  (w : (pIn : InChan Z)
      -> (pOut : OutChan (S Z))
      -> Spawned {m = ProcessM} MsgT MsgT)
->  (input : Vect len MsgT)
->  ProcessM (List MsgT) (Live []) End
farm4RR2 nw w input = 
    do
        res <- spawnN 0 nw MsgT MsgT pRR
        roundRobin MsgT input (convertChansRR res) 
        msgs <- roundRobinRec (length input) (inChans res)
        Return msgs

-}