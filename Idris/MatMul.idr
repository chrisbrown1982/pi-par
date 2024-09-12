module MatMul 

-- import ParLib

import public Data.Fin
import public Data.List
import public Data.Vect
import public Decidable.Equality



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
spawnN n Z toTy frmTy p = Return []
spawnN n (S num) toTy frmTy p = 
  do
    s <- Spawn toTy frmTy p 
    r <- spawnN (n+2) num toTy frmTy p 
    Return ((n ** s) :: r)

public export
sendN  : {n : Nat}
      -> {chs : Vect n (t ** StChanTy t)}
      -> (msgs  : (Vect len (m : Nat ** (t : Type ** (OutChan m, t)))))
      -> ProcessM
           ()
           (Live chs)
           (Live chs)
sendN [] = Return () 
sendN ((m ** (t ** (c, msg))) :: cs) = 
    do Send c msg 
       sendN cs
       Return () 

public export
recN : {chs : Vect n (t ** StChanTy t)}
    -> (msgTy : Type)
    -> (inChs : Vect len (m : Nat ** InChan m))
    -> ProcessM 
            (List msgTy) -- (m ** stIdxMsgTyIn chs m n))
            (Live chs) 
            (Live chs)
recN ty [] = Return []
recN ty ((m ** c) :: chs) = 
    do m1 <- Recv {-ty-} c
       msgs <- recN ty chs
       Return (m1 :: msgs)

p :  (pIn : InChan Z)
      -> (pOut : OutChan (S Z))
      -> Spawned {m = ProcessM} Nat Nat
p pIn pOut = do
                    x <- Recv {-Nat-} pIn
                    Send pOut 42
                    Halt

test : Process
test = 
    do 
        c <- Spawn Nat Nat p
        Send (fChan c) 42
        v <- Recv {-Nat-} frm
        Halt



convertChans : (t : Type) 
            -> Vect len (m : Nat ** (OutChan m, InChan (S m)))
            -> (msgs : Vect len t)
            -> Vect len (m : Nat ** (t : Type ** (OutChan m, t)))
convertChans t [] msgs = []
convertChans t ((m ** c) :: rest) (msg::msgs) = 
   (m ** (t ** (fChan c, msg))) :: convertChans t rest msgs 

inChans : Vect len (m : Nat ** (OutChan m, InChan (S m))) -> Vect len (n : Nat ** InChan n)
inChans [] = []
inChans ((m ** i)::chs) = ((m+1) ** i) :: inChans chs


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
        res <- spawnN 4 inTy outTy w
        sendN (convertChans inTy res input)
        msgs <- recN outTy (inChans res)
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
-}
 
w : (pIn : InChan cid)
 -> (pOut : OutChan (S cid))
 -> Spawned {m = ProcessM} Nat Nat
w pIn pOut = do 
                Halt 



hd : List a -> a 

tl : List a -> List a

zip1 : List a -> List a -> List (a, a)

transpose1 : List (List a) -> List (List a)
transpose1 ( [] :: n) = [] 
transpose1 b = 
    ( map (\x => hd x) b) :: transpose1 (map (\x => tl x) b)

red : Nat -> (Nat,Nat) -> Nat 
red pair sum = 
    (fst pair) * (snd pair) + sum 

dot_product : List Nat -> List Nat -> Nat 
dot_product a b = 
    foldl red 0 (zip1 a b)

multiply_row_by_col : List Nat -> List (List Nat) -> (List Nat) 
multiply_row_by_col row [] = []
multiply_row_by_col row (col_head :: col_rest) = 
    (dot_product row col_head) :: (multiply_row_by_col row col_rest)

multiply_internal : List (List Nat) -> List (List Nat) -> List (List Nat)
multiply_internal [] b = [] 
multiply_internal (head::rest) b = 
    (multiply_row_by_col head b) :: (multiply_internal rest b) 

multiply : List (List Nat) -> List (List Nat) -> List (List Nat)
multiply a b = multiply_internal a (transpose1 b)


eW :  List (List Nat)   
      -> (pIn : InChan Z)
      -> (pOut : OutChan (S Z))
      -> Spawned {m = ProcessM} Nat Nat
eW matB pIn pOut = do
                    x <- Recv {-Nat-} pIn
                    Send pOut (map (\y => multiply_by_row(y)) x)
                    Halt

farmTest : Process 
farmTest = 
    do 
       res <- spawnN 0 4 Nat Nat (eW (transpose matB))
       sendN (convertChans Nat res (chunk (matA) 250))
       msgs <- recN Nat (inChans res)
       Halt