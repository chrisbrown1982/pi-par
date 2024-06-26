module Skel

import Main


spawnN : {chs : Vect nChs StChanTy}
      -> (n : Nat)
      -> (toTy : List Type)
      -> (frmTy : List Type)
      -> (p   : (pIn  : InChan  Z)
            -> (pOut : OutChan (S Z))
            -> Spawned {m = ProcessM} toTy frmTy)
      -> ProcessM
          (List (n ** (OutChan n, InChan (S n))))
          (Live chs scs)
          (spawnSFN n toTy frmTy chs scs)
spawnN {nChs} Z toTy frmTy p = Pure (Z ** [])
spawnN {nChs} (S n) toTy frmTy p = do
    (to,frm) <- Spawn toTy frmTy p
    xs <- spawnN n toTy frmTy p
    Pure (nChs ** (to,frm) :: xs)

{- farm : (worker : InChanTy n [Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat] 
              -> OutChanTy m [Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat] 
              -> Spawned to frm) 
    -> (nw : Nat) 
    -> (inL : List Nat) 
-> Process -}
farm : (worker : InChan 0 -> OutChan 1 -> Spawned {m=ProcessM} [List Nat] 
                                                               [List Nat])
   -> (inL : List Nat) 
   -> Process 
farm worker inL = 
    do

        {-
        (toW1, frmW1) <- Spawn [List Nat]
                               [List Nat] worker 

   
        (toW2, frmW2) <- Spawn [List Nat] 
                               [List Nat] worker 

    
        (toW3, frmW3) <- Spawn [List Nat] 
                               [List Nat] worker 

        (toW4, frmW4) <- Spawn [List Nat] 
                               [List Nat] worker 
    -}
        xs <- spawnN 4 [List Nat] [List Nat] worker
    
        ?after2 
        -- Send (index 0 toChans) [1,2,3] -- (replicate 10 42)
     --   Send (fst (index 1 chans)) (replicate 10 42)
     --   Send (fst (index 2 chans)) (replicate 10 42)
     --   Send (fst (index 3 chans)) (replicate 10 42)


       {- r1 <- Recv frmW1
        r2 <- Recv frmW2
        r3 <- Recv frmW3
    r4 <- Recv frmW4 -}

       