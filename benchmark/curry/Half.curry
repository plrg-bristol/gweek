-- Half of a Peano number via inverse computation
-- Equivalent to benchmark/gweek/half.gwk

import Control.Search.Unsafe (allValues)

data Nat = Z | S Nat

addNat :: Nat -> Nat -> Nat
addNat Z     p = p
addNat (S p) q = S (addNat p q)

half :: Nat -> Nat
half y | addNat x x =:= y = x where x free

mul :: Nat -> Nat -> Nat
mul Z     _ = Z
mul (S p) q = addNat q (mul p q)

-- 1600 = 16 * 10 * 10
n10 :: Nat
n10 = S (S (S (S (S (S (S (S (S (S Z)))))))))              -- 10

n1600 :: Nat
n1600 = mul (S (S (S (S (S (S (S (S                         -- 16
            (S (S (S (S (S (S (S (S Z))))))))))))))))
            (mul n10 n10)                                   -- * 100

count :: Int
count = length (allValues (half n1600))

main :: IO ()
main = print count >> putStrLn " solutions"
