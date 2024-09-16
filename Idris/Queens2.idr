module Queens2

import Data.List

hd : List a -> a 
andB : Bool -> Bool -> Bool
zipIt : List Nat -> List Nat -> List (Nat, Nat)
app : List Nat -> List Nat -> List Nat


check : (Nat, Nat) -> (Nat,Nat) -> Bool 
check (c,l) (i,j) = (l == j) || ((c+l) == (i+j)) || ((minus c l) == (minus i j))

safe : List Nat -> Nat -> Bool 
safe p n = 
    foldr andB True ([ not (check (i,j) (length p + 1,n)) | (i,j) <- (zipIt [1..length p]  p)])

rainhas2 : Nat -> Nat -> Nat -> List (List Nat)
rainhas2 Z linha numero = [[]]
rainhas2 m linha numero = 
    [ app p [n] | p <- rainhas2 (minus m 1) linha numero, n <- ([linha .. numero] ++ [1..minus linha 1]), safe p n]


prainhas : Nat -> Nat -> List (List Nat)
prainhas numero linha = rainhas2 numero linha numero 


search : Nat -> Nat -> List (List Nat)
search numero n = takeWhile (\a => hd a == n) (prainhas numero n)

rainhas : Nat -> List (List (List Nat))
rainhas n = map (\x => search n x) [1..n]
