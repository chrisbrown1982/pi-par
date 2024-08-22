module Skel2

import Main2


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

plusMultZ : (n : Nat) -> n = plus n (mult 0 2)

--- %logging "eval" 5

public export
SpawnN : {n : Nat}
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
          -- (List (m ** (OutChan m, InChan (S m))))
          ()
          (Live chs scs)
          (const2 (SpawnSFN num toTy frmTy chs scs ()))
SpawnN {n} {m} {chs} {scs} Z toTy frmTy p = rewrite sym (plusMultZ n) in Pure2 () 
SpawnN {n} {m} {chs} {scs} (S num) toTy frmTy p
  = let r = Pure2 {stFn = const2 (SpawnSFN (S num) toTy frmTy chs scs ())} () in r 


{-
spawnN Z {chs=[]} {scs} toTy frmTy p = ?h -- Pure () -- (Prelude.Nil)
spawnN Z {chs=(_::_)} {scs} toTy frmTy p = ?h2 -- Pure () -- []
spawnN (S Z) {nChs} {chs} {scs} toTy frmTy p 
    (to,frm) <- Spawn toTy frmTy p
    Pure () -- [(nChs ** (to, frm))]
spawnN (S (S n')) {nChs} {chs} {scs} toTy frmTy p = do
    ?ahh


    -- (to,frm) <- Spawn toTy frmTy p

    -- ?h3

    -- spawnN (S n') toTy frmTy p

    -- xs <- spawnN (S n') toTy frmTy p
    --  | _ => assert_total $ idris_crash "no"
    -- let interm = (_ ** (to, frm)) :: (d :: ds) 
    -- ?afterKK
    -- ?h -- interm
    Pure () -- ((_ ** (to, frm)) :: xs)
{-
    case n' of 
        Z => ?after991 -- Pure [(nChs ** (to, frm))]
        (S n'') => ?after992 -- Pure ((nChs ** (to, frm)) :: xs)
    -- Pure xs
    -- ?after99
%logging off
-}

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

       