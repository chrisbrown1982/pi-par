module New

import Data.Fin
import Data.List
import Data.Vect

-------------------------------------------------------------------------------
-- Channels

data Loc : Nat -> Type where
  Here  : Loc Z
  There : Loc n -> Loc (S n)

data InChan : Nat -> Type where
  MkIn : {n : Nat} -> Loc n -> InChan n

data OutChan : Nat -> Type where
  MkOut : {n : Nat} -> Loc n -> OutChan n

data Chan : Type where
  MkInChan  : {n : Nat} -> InChan n  -> Chan
  MkOutChan : {n : Nat}
           -> OutChan n
           -- (ts -> (relinquishing, retaining))
           -> Maybe (List Type -> (List Type, List Type))
           -> Chan

fromChan : Chan -> Nat
fromChan (MkInChan {n} _) = n
fromChan (MkOutChan {n} _ _) = n

data InChanTy : List Type -> Type where
  MkInChanTy : (ts : List Type) -> InChanTy ts
data OutChanTy : List Type -> Type where
  MkOutChanTy : (ts : List Type) -> OutChanTy ts

data StChanTy : Type where
  SendTy : List Type -> StChanTy
  RecvTy : List Type -> StChanTy

-------------------------------------------------------------------------------
-- State Definition & Management Operations

-- Type representing the state of the process in terms of channels.
-- A Process is either active or halted.
-- A halted process cannot be restarted.
-- An active process manages its set of live channels.
data State : Type where
  Live : {n : Nat} -> (chs : Vect n StChanTy) -> State
  End  : State
  -- Option: transition to End only permitted when all Channels are spent

stIdxMsgTyOut : {n : Nat} -> (chs : Vect n StChanTy) -> (ch  : Nat) -> Type
stIdxMsgTyOut [] ch = Void
stIdxMsgTyOut (SendTy [] :: chs) Z = Void
stIdxMsgTyOut (SendTy (t :: ts) :: chs) Z = t
stIdxMsgTyOut (RecvTy _  :: chs) Z = Void
stIdxMsgTyOut (hd        :: chs) (S ch) = stIdxMsgTyOut chs ch

stIdxMsgTyIn : {n : Nat} -> (chs : Vect n StChanTy) -> (ch,i : Nat) -> Type
stIdxMsgTyIn [] ch i = Void
stIdxMsgTyIn (SendTy _  :: chs) Z i = Void
stIdxMsgTyIn (RecvTy [] :: chs) Z i = Void
stIdxMsgTyIn (RecvTy (InChanTy ss :: ts) :: chs) Z i = InChan i
stIdxMsgTyIn (RecvTy (OutChanTy ss :: ts) :: chs) Z i = OutChan i
stIdxMsgTyIn (RecvTy (t :: ts) :: chs) Z i = t
stIdxMsgTyIn (hd        :: chs) (S ch) i = stIdxMsgTyIn chs ch i

stIdxMsgTyInRaw : {n : Nat} -> (chs : Vect n StChanTy) -> (ch : Nat) -> Type
stIdxMsgTyInRaw [] ch = Void
stIdxMsgTyInRaw (SendTy _  :: chs) Z = Void
stIdxMsgTyInRaw (RecvTy [] :: chs) Z = Void
stIdxMsgTyInRaw (RecvTy (t :: ts) :: chs) Z = t
stIdxMsgTyInRaw (hd        :: chs) (S ch) = stIdxMsgTyInRaw chs ch

tail' : List a -> List a
tail' [] = []
tail' (x :: xs) = xs

stDecAt : {n : Nat} -> (chs : Vect n StChanTy) -> (ch : Nat) -> Vect n StChanTy
stDecAt [] ch = [] -- no change
stDecAt (SendTy ts :: chs) Z = SendTy (tail' ts) :: chs
stDecAt (RecvTy ts :: chs) Z = RecvTy (tail' ts) :: chs
stDecAt (ch :: chs) (S k) = ch :: stDecAt chs k

stEmptyAt : {n : Nat}
         -> (chs : Vect n StChanTy)
         -> (ch : Nat)
         -> Vect n StChanTy
stEmptyAt [] ch = []
stEmptyAt (SendTy ts :: chs) Z = SendTy [] :: chs
stEmptyAt (RecvTy ts :: chs) Z = RecvTy [] :: chs
stEmptyAt (ch :: chs) (S k) = ch :: stEmptyAt chs k

-- ...this is map.
stApplyAt : (f   : List Type -> List Type)
         -> (chs : Vect n StChanTy)
         -> (ch  : Nat)
         -> Vect n StChanTy
stApplyAt f [] ch = []
stApplyAt f (SendTy ts :: chs) Z = SendTy (f ts) :: chs
stApplyAt f (RecvTy ts :: chs) Z = RecvTy (f ts) :: chs
stApplyAt f (ch :: chs) (S k) = ch :: stApplyAt f chs k

stSplitAt : {n : Nat}
         -> (chs : Vect n StChanTy)
         -> (ch : Chan)
         -> Vect n StChanTy
stSplitAt chs (MkInChan {n} _) = stEmptyAt chs n
stSplitAt chs (MkOutChan {n} _ Nothing) = stEmptyAt chs n
stSplitAt chs (MkOutChan {n} _ (Just f)) = stApplyAt (snd . f) chs n

stOutChBTy : {n : Nat}
          -> (f : List Type -> (List Type, List Type))
          -> (chs : Vect n StChanTy)
          -> (i : Nat)
          -> Type
stOutChBTy f [] i = Void -- invalid channel
stOutChBTy f (RecvTy ts :: chs) Z = Void -- wrong direction
stOutChBTy f (SendTy ts :: chs) Z = OutChanTy (fst (f ts))
stOutChBTy f (_ :: chs) (S k) = stOutChBTy f chs k

stInChBTy : {n : Nat}
         -> (chs : Vect n StChanTy)
         -> (i : Nat)
         -> Type
stInChBTy [] i = Void -- invalid channel
stInChBTy (RecvTy ts :: chs) Z = InChanTy ts
stInChBTy (SendTy ts :: chs) Z = Void
stInChBTy (_ :: chs) (S k) = stInChBTy chs k

-------------------------------------------------------------------------------
-- State Transition Functions

spawnSF : {t : Type}
       -> {n : Nat}
       -> (to,frm : List Type)
       -> (chs    : Vect n StChanTy)
       -> (x : t)
       -> State
spawnSF to frm chs _ = Live (chs ++ [SendTy to, RecvTy frm])

serialSF : {t : Type}
        -> {n : Nat}
        -> (f : List Type -> (List Type, List Type))
        -> (ch : Nat)
        -> (chs : Vect n StChanTy)
        -> (x : t)
        -> State
serialSF {t = Void} f ch chs x with (x)
  serialSF {t = Void} f ch chs x | p impossible
serialSF {t} f ch chs x = Live (stApplyAt (snd . f) chs ch)

sendSF : {t : Type}
      -> {n : Nat}
      -> (ch  : Nat)
      -> (chs : Vect n StChanTy)
      -> (msgTy : Type)
      -> (msg : msgTy)
      -> (x : t)
      -> State
sendSF ch chs Void msg x with (msg)
  sendSF ch chs Void msg x | p impossible
sendSF ch chs Chan msg x = Live (stSplitAt (stDecAt chs ch) msg)
sendSF ch chs msgTy msg x = Live (stDecAt chs ch)

recvSF : {t : Type}
      -> {n : Nat}
      -> (ch : Nat)
      -> (chs : Vect n StChanTy)
      -> (ty : Type)
      -> (x : t)
      -> State
recvSF {t = Void} ch chs ty x with (x)
  recvSF {t = Void} ch chs ty x | p impossible
recvSF {t = Chan} ch chs ty x = Live chs -- FIXME
recvSF {t} ch chs (OutChanTy ts) x = Live ((stDecAt chs ch) ++ [(SendTy ts)])
recvSF {t} ch chs (InChanTy ts) x = Live ((stDecAt chs ch) ++ [(RecvTy ts)])
recvSF {t} ch chs ty x = Live (stDecAt chs ch)

-------------------------------------------------------------------------------
-- Monad/State Machine Definition

Spawned : {m : (ty : Type) -> (st : State) -> (ty -> State) -> Type}
       -> (inTy  : List Type)
       -> (outTy : List Type)
       -> Type
Spawned {m} inTy outTy =
  m () (Live [(RecvTy inTy), (SendTy outTy)]) (const End)

data ProcessM : (ty : Type) -> (st : State) -> (ty -> State) -> Type where
  -- DSL operations
  Spawn : {chs : Vect n StChanTy}   
       -> (to  : List Type)
       -> (frm : List Type)
       -> (tmpInTy,tmpOutTy : List Type)
       -> (p   : (pIn  : InChan  Z)
              -> (pOut : OutChan (S Z))
              -> Spawned {m = ProcessM} tmpInTy tmpOutTy)
       -> ProcessM (OutChan n, InChan (S n))
                   (Live chs)
                   (spawnSF to frm chs)
  SOutC : {chs : Vect n StChanTy}
       -> (ch : OutChan m)
       -> (f  : List Type -> (List Type, List Type))
                          -- (relinquishing, retaining)
       -> ProcessM (stOutChBTy f chs m)
                   (Live chs)
                   (serialSF f m chs)
  SInC  : {chs : Vect n StChanTy}
       -> (ch  : InChan m)
       -> ProcessM (stInChBTy chs m)
                   (Live chs)
                   (serialSF (\ts => (ts,[])) m chs)
  Send  : {chs : Vect n StChanTy}
       -> {m   : Nat}
       -> (ch  : OutChan m)
       -> (msg : stIdxMsgTyOut chs m)
       -> ProcessM () (Live chs) (sendSF m chs (stIdxMsgTyOut chs m) msg)
  Recv  : {chs : Vect n StChanTy}
       -> {m   : Nat}
       -> (ch  : InChan m)
       -> ProcessM
            (stIdxMsgTyIn chs m n)
            (Live chs)
            (recvSF m chs (stIdxMsgTyInRaw chs m))
  Halt  : ProcessM () (Live chs) (const End)
  -- Standard operations
  Pure  : (x : t) -> ProcessM t st (const st)
  (>>=) : ProcessM a (Live chs) sf 
       -> ((x : a) -> ProcessM b (sf x) s3f)
       -> ProcessM b (Live chs) s3f
  (>>)  : ProcessM () (Live chs) sf
       -> ProcessM b (sf ()) s3f
       -> ProcessM b (Live chs) s3f

Process : Type
Process = ProcessM () (Live []) (const End)

-------------------------------------------------------------------------------
-- Example

{-
calc : Process
calc =
  do
    (toP,frmP) <- Spawn [Nat, Nat] [Nat] [Nat, Nat] [Nat] p
    (toQ,frmQ) <- Spawn [OutChanTy [Nat]] [] [OutChanTy [Nat]] [] q
    Send toP Z
    -- Send toQ  -- (MkOutChan toP (Just (\ts => (take 1 ts, drop 1 ts))))
    ?after
    -- Halt
  where
    p : (pIn  : InChan  Z)
     -> (pOut : OutChan (S Z))
     -> Spawned {m = ProcessM} [Nat, Nat] [Nat]
    p pIn pOut = do
      x <- Recv pIn
      -- x <- Recv (MkIn (There Here))
      ?afterP
      -- Halt

    q : (qIn  : InChan  Z)
     -> (qOut : OutChan (S Z))
     -> Spawned {m = ProcessM} [OutChanTy [Nat]] []
    q qIn qOut = do
      toP <- Recv qIn
      Send toP Z
      ?afterQ
      -- Halt
-}

test : Process
test =
  do
    (toP,frmP) <- Spawn [Nat] [InChanTy [Nat,Nat]] [Nat] [InChanTy [Nat,Nat]] p
    (toQ,frmQ) <- Spawn [InChanTy [Nat,Nat]] [] [InChanTy [Nat,Nat]] [] q
    ch <- Recv frmP
    -- toP' <- SOutC (MkOut (There Here)) (\ts => (ts,[]))
    -- ch' <- SOutC ch (\ts => (take 1 ts, drop 1 ts))
    ch' <- SInC ch
    Send toQ ch'
    ?after
    -- Halt
  where
    p pIn pOut = Halt
    q qIn qOut = Halt


-- problem : you can now send toP' multiple times
-- solution: keep track of what serialised things we have sent
-- you can only send a serialised channel once
-- we will need to extend our Live state...

-- what happens if you serialise something to simply remove some behavioural prefix? The receiver will still expect certain things to be sent (first) so you can't avoid it.

-------------------------------------------------------------------------------

{-
  main = do
    (to, frm) <- spawn [Nat, Nat] [Nat] p
    send to 1
    send to 2
    ans <- recv frm
    halt
-}

