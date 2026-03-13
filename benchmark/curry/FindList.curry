-- Find all lists of length 7 whose elements sum to 5
-- Equivalent to examples/find_list.gwk

import Control.Search.Unsafe (allValues)

data Nat = Z | S Nat

addNat :: Nat -> Nat -> Nat
addNat n Z     = n
addNat n (S z) = S (addNat n z)

sumNat :: [Nat] -> Nat
sumNat []     = Z
sumNat (z:zs) = addNat z (sumNat zs)

lengthNat :: [Nat] -> Nat
lengthNat []     = Z
lengthNat (_:zs) = S (lengthNat zs)

goal :: [Nat]
goal | lengthNat xs =:= S (S (S (S (S (S (S Z)))))) &  -- length 7
       sumNat xs =:= S (S (S (S (S Z)))) = xs          -- sum 5
  where xs free

count :: Int
count = length (allValues goal)

main :: IO ()
main = print count >> putStrLn " solutions"
