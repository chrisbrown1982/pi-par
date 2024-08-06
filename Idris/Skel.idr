module Skel

import Main3


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


--- %logging "eval" 5
public export
spawnN : {n : Nat}
      -> {m : Nat}
      -> {chs : Vect n StChanTy}
      -> {scs : Vect m Nat} 
      -> (num : Nat)
      -> (toTy : List Type)
      -> (frmTy : List Type)
      -> (p  : (pIn  : InChan  Z)
            -> (pOut : OutChan (S Z))
            -> Spawned {m = ProcessM} toTy frmTy)
      -> ProcessM
          (List (m ** (OutChan m, InChan (S m))))
          (Live chs scs)
          (spawnSFN num toTy frmTy chs scs)
spawnN Z toTy frmTy p = Pure []
spawnN {n} {chs} {scs} (S n') toTy frmTy p 
    = do
         (to, frm) <- Spawn toTy frmTy p
         xs <- spawnN n' toTy frmTy p
         Pure ((n ** (to, frm)) :: xs)

data SendNP : (scs : Vect k Nat) -> (chs : Vect n StChanTy) -> (chsS : Vect len (m : Nat ** OutChan m)) -> (msgT : Type) -> Type where
    SNPNil  : SendNP scs chs [] msgT
    SNPCons : SendNP scs chs chsS ty
           -> SendNP scs chs ((m ** ch) :: chsS) (stIdxMsgTyOut scs chs m)

sendN  : {chs : Vect n StChanTy}
      -> {scs : Vect k Nat}
      -- -> {m   : Nat}
      -> {msgT : Type}
      -> (msgs : Vect len  msgT)
      -> (chsS  : (Vect len (m : Nat ** OutChan m)))
      -> (ok   : SendNP scs chs chsS msgT) 
    --  -> (msgs : List (stIdxMsgTyOut scs chs m))
      -> ProcessM
           ()
           (Live chs scs)
           (sendSFN chs scs chsS chs)
sendN msgs [] p = Pure ()
sendN (msg::ms) ((m ** c)  ::cs) (SNPCons p) = 
    do  Send c msg
        -- sendN ms cs ?hp
        ?h2

farm : (worker : InChan 0 -> OutChan 1 
         -> Spawned {m=ProcessM} [List Nat] 
                                 [List Nat])
   -> (inL : List Nat) 
   -> Process
farm worker inL = 
    do
        xs <- spawnN 4 [List Nat] [List Nat] worker

        case xs of 
            [] => Halt
            ((n ** p) :: ds) => ?after2
    
        -- ?after2 
        -- Send (index 0 toChans) [1,2,3] -- (replicate 10 42)
     --   Send (fst (index 1 chans)) (replicate 10 42)
     --   Send (fst (index 2 chans)) (replicate 10 42)
     --   Send (fst (index 3 chans)) (replicate 10 42)


       {- r1 <- Recv frmW1
        r2 <- Recv frmW2
        r3 <- Recv frmW3
    r4 <- Recv frmW4 -}

       