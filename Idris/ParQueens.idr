module ParQueens

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

hd : List a -> a 
andB : Bool -> Bool -> Bool
zipIt : List Nat -> List Nat -> List (Nat, Nat)
app : List Nat -> List Nat -> List Nat

check : (Nat, Nat) -> (Nat,Nat) -> Bool 
check (c,l) (i,j) = (l == j) || ((c+l) == (i+j)) || ((minus c l) == (minus i j))

safe : List Nat -> Nat -> Bool 
safe p n = 
    foldr andB True ([ not (check (i,j) (length p + 1,n)) | (i,j) <- (zipIt [1..length p]  p)])

rainhas2 : Nat -> Nat -> Nat -> List (List Nat)
rainhas2 Z linha numero = [[]]
rainhas2 m linha numero = 
    [ app p [n] | p <- rainhas2 (minus m 1) linha numero, n <- ([linha .. numero] ++ [1..minus linha 1]), safe p n]

prainhas : Nat -> Nat -> List (List Nat)
prainhas numero linha = rainhas2 numero linha numero 

search : Nat -> Nat -> List (List Nat)
search numero n = takeWhile (\a => hd a == n) (prainhas numero n)

rainhas : Nat -> List (List (List Nat))
rainhas n = map (\x => search n x) [1..n]

pRR :  (pIn : InChan Z)
    -> (pOut : OutChan (S Z))
    -> Spawned {m = ProcessM} MsgT MsgT
pRR pIn pOut = do
        x <- Recv MsgT pIn
        case x of 
            Msg m => do Send pOut (search 5 m)
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
        msgs <- roundRobinRec (minus (length input) 1) (inChans res)
        Return msgs
        
