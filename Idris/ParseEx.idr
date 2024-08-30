module ParseEx

id : Nat -> Nat
id x = x

const : Nat -> Nat -> Nat
const x y = x

mainPar : IO ()
mainPar = do
  printLn "Hello World"
