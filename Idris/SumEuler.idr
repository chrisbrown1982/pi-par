module SumEuler

import ParLib

rem : Nat -> Nat -> Nat

gcd2 : Nat -> Nat -> Nat 
gcd2 a 0 = a 
gcd2 a b = gcd2 b (a `rem` b)



relPrime : Nat -> Nat -> Bool
relPrime x y = (gcd2 x y) == 1 


mkList : Nat -> List Nat 
mkList n = [1..n]


euler : Nat -> Nat 
euler n = 
    length ( filter (\x => relPrime n x) (mkList n))


sumEuler : Nat -> Nat 
sumEuler n = 
    sum ( map (\x => euler(x)) (mkList n))

