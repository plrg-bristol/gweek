-- All permutations of [1..7]
-- Equivalent to benchmark/gweek/perm_simple.gwk

import Control.Search.Unsafe (allValues)

data Nat = Z | S Nat

insert :: Nat -> [Nat] -> [Nat]
insert x []     = [x]
insert x (z:zs) = (x : z : zs) ? (z : insert x zs)

perm :: [Nat] -> [Nat]
perm []     = []
perm (z:zs) = insert z (perm zs)

goal :: [Nat]
goal = perm [S Z,                             -- 1
             S (S Z),                         -- 2
             S (S (S Z)),                     -- 3
             S (S (S (S Z))),                 -- 4
             S (S (S (S (S Z)))),             -- 5
             S (S (S (S (S (S Z))))),         -- 6
             S (S (S (S (S (S (S Z))))))]     -- 7

count :: Int
count = length (allValues goal)

main :: IO ()
main = print count >> putStrLn " solutions"
