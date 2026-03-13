-- Last element of a list via unification
-- Equivalent to benchmark/gweek/last.gwk

import Control.Search.Unsafe (allValues)

data Nat = Z | S Nat

lastElem :: [Nat] -> Nat
lastElem l | xs ++ [x] =:= l = x where xs, x free

goal :: Nat
goal = lastElem (replicate 100 (S Z))

count :: Int
count = length (allValues goal)

main :: IO ()
main = print count >> putStrLn " solutions"
