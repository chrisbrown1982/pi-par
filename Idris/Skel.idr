module Skel

import Main


{-Spawn : {chs : Vect n StChanTy}
       -> {scs : Vect m Nat}
       -> (to  : List Type)
       -> (frm : List Type)
       -> (p   : (pIn  : InChan  Z)      -- channel position in the child
              -> (pOut : OutChan (S Z))  
              -> Spawned {m = ProcessM} to frm)
       -> ProcessM (OutChan n, InChan (S n))
                   (Live chs scs)
                   (spawnSF to frm chs scs)
-}


spawnN : (n : Nat)
      -> {nChs : Nat}
      -> {chs : Vect nChs StChanTy}
      -> {scs : Vect m Nat}
      -> (toTy : List Type)
      -> (frmTy : List Type)
      -> (p  : (pIn  : InChan  Z)
            -> (pOut : OutChan (S Z))
            -> Spawned {m = ProcessM} toTy frmTy)
      -> ProcessM
          (List (m ** (OutChan m, InChan (S m))))
          (Live chs scs)
          (spawnSFN n toTy frmTy chs scs)
spawnN Z {chs=[]} {scs} toTy frmTy p = Pure (Prelude.Nil)
spawnN Z {chs=(_::_)} {scs} toTy frmTy p = ?afterPP
spawnN {nChs} (S n) {chs} {scs} toTy frmTy p = do
    (to,frm) <- Spawn toTy frmTy p
    xs <- spawnN n toTy frmTy p
    case n of 
        Z => ?after991 -- Pure [(nChs ** (to, frm))]
        (S n') => Pure ((nChs ** (to, frm)) :: xs)
    -- Pure xs
    -- ?after99

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
        -- xs <- spawnN 4 [List Nat] [List Nat] worker
    
        ?after2 
        -- Send (index 0 toChans) [1,2,3] -- (replicate 10 42)
     --   Send (fst (index 1 chans)) (replicate 10 42)
     --   Send (fst (index 2 chans)) (replicate 10 42)
     --   Send (fst (index 3 chans)) (replicate 10 42)


       {- r1 <- Recv frmW1
        r2 <- Recv frmW2
        r3 <- Recv frmW3
    r4 <- Recv frmW4 -}

       