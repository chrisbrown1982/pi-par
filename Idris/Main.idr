module Main

import Data.Fin
import Data.Vect

-------------------------------------------------------------------------------
-- Direction

data Dir : Type where
  In  : Dir
  Out : Dir

-------------------------------------------------------------------------------
-- Channels

{-
data Loc : Type where
  Ptr : {b : Nat} -> Fin b -> Loc

data InChan : Type where
  MkIn : Loc -> InChan

data OutChan : Type where
  MkOut : Loc -> OutChan
 -}

data Loc : Nat -> Type where
  Hic : Loc Z
  Ibi : Loc n -> Loc (S n)

-------------------------------------------------------------------------------
-- Monad/State Machine

-- Direction, Tokens, Carrier Type
record Chan where
  constructor MkChan
  direction : Dir
  bound     : Nat
  msgType   : Type

data MState : Type where
  MkState : {n : Nat} -> (chs : Vect n Chan) -> MState
  End : MState

data Proc : Type where
  TODO_Proc : Proc

spawnSF : {n : Nat}
       -> (inB, outB : Nat)
       -> (inTy, outTy : Type)
       -> (chs : Vect n Chan)
       -> (x : t)
       -> MState
spawnSF inB outB inTy outTy chs x =
  MkState (chs ++ [(MkChan In inB inTy), (MkChan Out outB outTy)])

interface Idx (0 opM : (t : Type) -> MState -> (t -> MState) -> Type) where
  indexTy : {n : Nat}
         -> (chs : Vect n Chan)
         -> (ch  : Nat)
         -> Type
  -- index' : (chs : Vect n Chan)
  --       -> (ch  : Loc m)
  --       -> (indexTy chs ch)
  toNat : {m : Nat} -> Loc m -> Nat
  toNat {m} _ = m

mutual
  sendSF : {m,n : Nat}
        -> (chs : Vect n Chan)
        -> (ch  : Loc m)
        -> (x : t)
        -> MState
  sendSF {m} chs ch x =
    -- let r = indexTy {opM = MOp} chs m
    --     z = ?here
    -- in 
      MkState chs

-- mutual
  data MOp : (t : Type) -> (st : MState) -> (t -> MState) -> Type where
    Send  : {chs : Vect ub Chan}
         -> (ch  : Loc m)
        --  -> (msg : Nat)
         -> (msg : (indexTy {opM = MOp} chs (toNat {opM = MOp} ch)))
         -> MOp () (MkState chs) (sendSF chs ch)
    Recv  : MOp () (MkState chs) (const (MkState chs))
    Spawn : {chs : Vect b Chan}
        -> (inB : Nat) -> (inTy : Type)
        -> (outB : Nat) -> (outTy : Type)
        -> (p : Proc)
        -- -> MOp (Fin (S (S b)), Fin (S (S b))) -- restrict Fins?
        -> MOp (Loc b, Loc (S b)) -- restrict Fins? YES!
                (MkState chs)
                (spawnSF inB outB inTy outTy chs)

  implementation Idx MOp where
    indexTy [] ch = Void
    indexTy (ch :: _) Z = msgType ch
    indexTy (_ :: chs) (S ch) = indexTy {opM = MOp} chs ch

    -- index' chs ch = ?idxHole

data M : (ty : Type) -> (st : MState) -> (ty -> MState) -> Type where
  Pure   : (x : t) -> M t st (const st)
  Op     : MOp t st sf -> M t st sf
  (>>=)  : M a (MkState chs) sf 
        -> ((x : a)
        -> M b (sf x) s3f)
        -> M b (MkState chs) s3f
  (>>)   : M () (MkState chs) sf
        -> M b (sf ()) s3f
        -> M b (MkState chs) s3f
  -- 
  Init   : M () (MkState []) (const (MkState []))
  Halt   : M () st (const End)
  
  
test : M () (MkState []) (const End)
test = do
  -- ?here
  Init
  (to, frm) <- Op (Spawn 2 Nat 1 Nat TODO_Proc)
  let ch : Loc 3 = Ibi (Ibi (Ibi Hic))
  Op (Send to 1)
  ?after
  Halt
  -- ?here
  -- Op Send
  -- Op Recv



-------------------------------------------------------------------------------

{-
  main = do                             []
    (to, frm) <- spawn 2 Nat 1 Nat p    [(Out, 2, Nat),(In, 1, Nat)]
    send to 1                           [(Out, 1, Nat),(In, 1, Nat)]
    send to 1                           [(Out, 0, Nat),(In, 1, Nat)]
    ans <- recv fm                      [(Out, 0, Nat),(In, 0, Nat)]
-}

