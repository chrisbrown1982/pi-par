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

data InChan : Nat -> Type where
  MkIn : {n : Nat} -> Loc n -> InChan n

data OutChan : Nat -> Type where
  MkOut : {n : Nat} -> Loc n -> OutChan n

-------------------------------------------------------------------------------
-- Monad/State Machine

-- Direction, Tokens, Carrier Type
record Chan where
  constructor MkChan
  -- direction : Dir
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
  MkState (chs ++ [(MkChan inB inTy), (MkChan outB outTy)])

interface Idx (0 opM : (t : Type) -> MState -> (t -> MState) -> Type) where
  indexTy : {n : Nat}
         -> (chs : Vect n Chan)
         -> (ch  : Nat)
         -> Type

  decAt : {n : Nat}
       -> (chs : Vect n Chan)
       -> (ch : Nat)
       -> Vect n Chan

  toNat : {m : Nat} -> Loc m -> Nat
  toNat {m} _ = m

  toNatOut : {m : Nat} -> OutChan m -> Nat
  toNatOut {m} _ = m

  toNatIn : {m : Nat} -> InChan m -> Nat
  toNatIn {m} _ = m

-- data IsValid : Type -> Type where
--   ItIs : IsValid Void

notVoid : Type -> Bool
notVoid Void = False
notVoid _    = True

mutual
  sendSF : {m,n : Nat}
        -> (chs : Vect n Chan)
        -> (ch  : OutChan m)
        -> (x : t)
        -> MState
  sendSF {m} chs ch x = MkState (decAt {opM = MOp} chs m)

  recvSF : {m,n : Nat}
        -> (chs : Vect n Chan)
        -> (ch  : InChan m)
        -> (x   : t)
        -> MState
  recvSF {m} chs ch x = MkState (decAt {opM = MOp} chs m)

-- mutual
  data MOp : (t : Type) -> (st : MState) -> (t -> MState) -> Type where
    Send  : {chs : Vect ub Chan}
         -> (ch  : OutChan m)
        --  -> (msg : Nat)
         -> (msg : (indexTy {opM = MOp} chs (toNatOut {opM = MOp} ch)))
         -> MOp () (MkState chs) (sendSF chs ch)
    Recv  : {chs : Vect ub Chan}
         -> (ch  : InChan m)
         -> {auto chk :
              So (notVoid (indexTy {opM = MOp} chs (toNatIn {opM = MOp} ch)))}
         -> MOp
              (indexTy {opM = MOp} chs (toNatIn {opM = MOp} ch))
              (MkState chs)
              (recvSF chs ch)
    Spawn : {chs : Vect b Chan}
        -> (inB : Nat) -> (inTy : Type)
        -> (outB : Nat) -> (outTy : Type)
        -> (p : Proc)
        -- -> MOp (Fin (S (S b)), Fin (S (S b))) -- restrict Fins?
        -> MOp (OutChan b, InChan (S b)) -- restrict Fins? YES!
                (MkState chs)
                (spawnSF inB outB inTy outTy chs)

  implementation Idx MOp where
    indexTy [] ch = Void
    indexTy (MkChan Z _ :: _) Z = Void
    indexTy (ch :: _) Z = msgType ch
    indexTy (_ :: chs) (S ch) = indexTy {opM = MOp} chs ch

    -- index' chs ch = ?idxHole

    decAt [] ch = []
    decAt (MkChan b t :: chs) Z = MkChan (pred b) t :: chs
    decAt (ch :: chs) (S k) = ch :: decAt {opM = MOp} chs k

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
  let ch : OutChan 3 = MkOut (Ibi (Ibi (Ibi Hic)))
  Op (Send to (S Z))
  Op (Send to (S Z))
  x <- Op (Recv frm)
  -- ?after
  Halt
  -- ?here
  -- Op Send
  -- Op Recv

{-
  1. Tidy up & fix Recv
  2. Delegation primitives
  3. Deal with Proc
  4. Skeleton example & usage
  5. Translate

-}


-------------------------------------------------------------------------------

{-
  main = do                             []
    (to, frm) <- spawn 2 Nat 1 Nat p    [(Out, 2, Nat),(In, 1, Nat)]
    send to 1                           [(Out, 1, Nat),(In, 1, Nat)]
    send to 1                           [(Out, 0, Nat),(In, 1, Nat)]
    ans <- recv fm                      [(Out, 0, Nat),(In, 0, Nat)]
-}

