-- N-Queens for 8x8 board using Peano naturals
-- Equivalent to examples/nqueens.gwk

import Control.Search.Unsafe (allValues)

data Nat = Z | S Nat

addNat :: Nat -> Nat -> Nat
addNat n Z     = n
addNat n (S z) = S (addNat n z)

neq :: Nat -> Nat -> Nat
neq Z     Z     = failed
neq Z     (S _) = Z
neq (S _) Z     = Z
neq (S m) (S n) = neq m n

safe :: Nat -> Nat -> [Nat] -> Nat
safe _ _ []     = Z
safe q d (r:rs) = case neq (addNat q d) r of
  Z -> case neq (addNat r d) q of
    Z     -> safe q (S d) rs
    (S _) -> failed
  (S _) -> failed

revappend :: [Nat] -> [Nat] -> [Nat]
revappend []     ys = ys
revappend (z:zs) ys = revappend zs (z : ys)

queens :: [Nat] -> [Nat] -> [Nat] -> [Nat]
queens skipped rest placed = case rest of
  [] -> case skipped of
    []    -> placed
    (_:_) -> failed
  (q:qs) ->
    (case safe q (S Z) placed of
       Z -> let remaining = revappend skipped qs in
            case remaining of
              []    -> q : placed
              (_:_) -> queens [] remaining (q : placed)
       (S _) -> failed)
    ?
    queens (q : skipped) qs placed

goal :: [Nat]
goal = queens [] [S Z,                                         -- 1
                  S (S Z),                                     -- 2
                  S (S (S Z)),                                 -- 3
                  S (S (S (S Z))),                             -- 4
                  S (S (S (S (S Z)))),                         -- 5
                  S (S (S (S (S (S Z))))),                     -- 6
                  S (S (S (S (S (S (S Z)))))),                 -- 7
                  S (S (S (S (S (S (S (S Z)))))))] []          -- 8

count :: Int
count = length (allValues goal)

main :: IO ()
main = print count >> putStrLn " solutions"
