module ParSumEuler2

import ParLib

import public Data.Fin
import public Data.List
import public Data.Vect
import public Decidable.Equality

data MsgT : Type where 
      MEnd : MsgT 
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
{- roundRobin msgT [] chs ((m ** c) :: chs2) =
      do Send c MEnd 
         roundRobin msgT [] chs chs2 
         Pure ()
-}
-- roundRobin msgT (ms::msgs) [] = roundRobin msgT (ms::msgs) chs2 chs2 
roundRobin msgT (ms::msgs) ((m ** c)::chs) = 
      do Send c ms 
         roundRobin msgT msgs (chs ++ [(m**c)]) 
         Pure ()

public export
roundRobinRec : 
      -- {len : Nat}
      {chs : Vect n (t ** StChanTy t)}
      -> (nMsgs : Nat)
      -> (chs2 :  Vect len (m : Nat ** (InChan m)))
   --   -> (chs3 : Vect len2 (m : Nat ** (InChan m)))
      -> ProcessM 
         (List MsgT)
         (Live chs)
         (Live chs)
roundRobinRec Z x = Pure []
roundRobinRec (S n) [] = Pure []
-- roundRobinRec Z [] chs2 = roundRobinRec Z chs2 chs2 
-- roundRobinRec Z ((m**c)::chs) chs2 = 
--      do m1 <- Recv MsgT c 
--         Pure (m1 :: [])
-- roundRobinRec (S n) [] chs2 = roundRobinRec (S n) chs2 chs2 
roundRobinRec (S n) ((m ** c)::chs) = 
      do m1 <- Recv MsgT c 
         msgs <- roundRobinRec n (chs ++ [(m**c)])
         Pure (m1 :: msgs)


public export
recNChan : {chs : Vect n (t ** StChanTy t)}
    -> (msgTy : Type)
    -> (inChs : Vect len (m : Nat ** InChan m))
    -> ProcessM 
            (List msgTy) -- (m ** stIdxMsgTyIn chs m n))
            (Live chs) 
            (Live chs)
recNChan ty [] = Pure []
recNChan ty ((m ** c) :: chs) = 
    do m1 <- Recv ty c
       msgs <- recNChan ty chs
       Pure (m1 :: msgs)


p :      (pIn : InChan Z)
      -> (pOut : OutChan (S Z))
      -> Spawned {m = ProcessM} Nat Nat
p pIn pOut = do
                    x <- Recv Nat pIn
                    Send pOut 42
                    Halt

test : Process
test = 
    do 
        c <- Spawn Nat Nat p
        Send (fChan c) 42
        v <- Recv Nat (sChan c)
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


rem : Nat -> Nat -> Nat

gcd2 : Nat -> Nat -> Nat 
gcd2 a 0 = a 
gcd2 a b = gcd2 b (a `rem` b)



relPrime : Nat -> Nat -> Bool
relPrime x y = (gcd2 x y) == 1 


mkList : Nat -> List Nat 
mkList n = [1..n]

mkMsg : List Nat -> List MsgT
mkMsg [] = [MEnd]
mkMsg (x::xs) = Msg x :: mkMsg xs


euler : Nat -> Nat 
euler n = 
    length ( filter (\x => relPrime n x) (mkList n))


sumEuler : Nat -> Nat 
sumEuler n = 
    sum ( map (\x => euler(x)) (mkList n))


pRR :  (pIn : InChan Z)
      -> (pOut : OutChan (S Z))
      -> Spawned {m = ProcessM} MsgT MsgT
pRR pIn pOut = do
                    x <- Recv MsgT pIn
                    case x of 
                        Msg m => do Send pOut (euler m)
                                    y <- pRR pIn pOut 
                                    Pure ()
                        MEnd => Halt
                                                    

farm4RR : (nW : Nat)
   ->  (input : Vect 4 MsgT)
   ->  ProcessM (List MsgT) (Live []) End
farm4RR nw input = 
    do
        res <- spawnN 0 4 MsgT MsgT pRR
        roundRobin MsgT input (convertChansRR res)
        msgs <- roundRobinRec (length input) (inChans res)
        Return msgs

{-
  farmTest : Process 
  farmTest = 
      do 
         res <- spawnN 0 4 Nat Nat eW
         sendN (convertChans Nat res (chunk (mkList 1000) 4))
         msgs <- recN Nat (inChans res)
         Halt
      -}


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
