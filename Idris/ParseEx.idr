module ParseEx

import ParLib

id : Nat -> Nat
id x = x

const : Nat -> Nat -> Nat
const x y = id x

{-
mainPar : IO ()
mainPar = do
  printLn "Hello World"
-}

-- {-
p1 : (cIn  : InChan  Z)
  -> (cOut : OutChan (S Z))
  -> Spawned {m = ProcessM} to frm
p1 cIn cOut = Halt

-- {-
mainPar : Process
mainPar = do
  (pTo, pFrm) <- Spawn Nat Nat p1
  msg <- Recv pFrm
  Halt
-- -}

-- TODO: translate Spawn
