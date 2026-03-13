-- Permutations of [1..7] where last element = 1
-- Equivalent to examples/perm.gwk

import Control.Search.Unsafe (allValues)

data Nat = Z | S Nat

natToInt :: Nat -> Int
natToInt Z     = 0
natToInt (S n) = 1 + natToInt n

intToNat :: Int -> Nat
intToNat 0 = Z
intToNat n = S (intToNat (n - 1))

insert :: Nat -> [Nat] -> [Nat]
insert x []     = [x]
insert x (z:zs) = (x : z : zs) ? (z : insert x zs)

perm :: [Nat] -> [Nat]
perm []     = []
perm (z:zs) = insert z (perm zs)

cat :: [Nat] -> [Nat] -> [Nat]
cat []     ys = ys
cat (x:xs) ys = x : cat xs ys

lastElem :: [Nat] -> Nat
lastElem xs | cat ys [y] =:= xs = y where ys, y free

goal :: [Nat]
goal | lastElem xs =:= intToNat 1 = xs
  where xs = perm [intToNat 1, intToNat 2, intToNat 3, intToNat 4,
                   intToNat 5, intToNat 6, intToNat 7]

count :: Int
count = length (allValues goal)

main :: IO ()
main = print count >> putStrLn " solutions"
