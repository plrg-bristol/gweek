-- Coin change: ways to make 20 using coins 1, 2, 10
-- Equivalent to examples/coins.gwk

import Control.Search.Unsafe (allValues)

data Nat = Z | S Nat

addNat :: Nat -> Nat -> Nat
addNat n Z     = n
addNat n (S z) = S (addNat n z)

coin :: Nat
coin = S Z              -- 1
     ? S (S Z)          -- 2
     ? S (S (S (S (S (S (S (S (S (S Z)))))))))  -- 10

change :: Nat -> [Nat]
change Z     = []
change (S m) | addNat c rest =:= S m = c : change rest
  where c = coin
        rest free

goal :: [Nat]
goal = change (S (S (S (S (S (S (S (S (S (S  -- 20
              (S (S (S (S (S (S (S (S (S (S
              Z))))))))))))))))))))

count :: Int
count = length (allValues goal)

main :: IO ()
main = print count >> putStrLn " solutions"
