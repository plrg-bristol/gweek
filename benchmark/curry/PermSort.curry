-- Permutation sort with Peano naturals
-- Equivalent to benchmark/gweek/permsort.gwk

import Control.Search.Unsafe (allValues)

data Nat = Z | S Nat

leq :: Nat -> Nat -> Nat
leq Z     _ = Z
leq (S _) Z = failed
leq (S m) (S n) = leq m n

insert :: Nat -> [Nat] -> [Nat]
insert x []     = [x]
insert x (z:zs) = (x : z : zs) ? (z : insert x zs)

perm :: [Nat] -> [Nat]
perm []     = []
perm (z:zs) = insert z (perm zs)

sorted :: [Nat] -> [Nat]
sorted []  = []
sorted [x] = [x]
sorted (x:y:ys) = case leq x y of
  Z -> x : sorted (y : ys)

psort :: [Nat] -> [Nat]
psort xs = sorted (perm xs)

goal :: [Nat]
goal = psort [S (S Z),                                         -- 2
              S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))),  -- 12
              S (S (S (S (S (S (S (S (S (S (S Z)))))))))),      -- 11
              S (S (S (S (S (S (S (S (S (S Z))))))))),          -- 10
              S (S (S (S (S (S (S (S (S Z)))))))),              -- 9
              S (S (S (S (S (S (S (S Z))))))),                  -- 8
              S (S (S (S (S (S (S Z)))))),                      -- 7
              S (S (S (S (S (S Z))))),                          -- 6
              S (S (S (S (S Z)))),                              -- 5
              S (S (S (S Z))),                                  -- 4
              S (S (S Z)),                                      -- 3
              S Z]                                              -- 1

count :: Int
count = length (allValues goal)

main :: IO ()
main = print count >> putStrLn " solutions"
