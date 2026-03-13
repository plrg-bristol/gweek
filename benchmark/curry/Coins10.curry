import Control.Search.Unsafe (allValues)

data Nat = Z | S Nat

addNat :: Nat -> Nat -> Nat
addNat n Z     = n
addNat n (S z) = S (addNat n z)

n1 :: Nat
n1 = S Z
n2 :: Nat
n2 = S n1
n10 :: Nat
n10 = S (S (S (S (S (S (S (S (S (S Z)))))))))

coin :: Nat
coin = n1 ? n2 ? n10

change :: Nat -> [Nat]
change Z     = []
change (S m) | addNat c rest =:= S m = c : change rest
  where c = coin
        rest free

goal :: [Nat]
goal = change n10

count :: Int
count = length (allValues goal)

main :: IO ()
main = print count >> putStrLn " solutions"
