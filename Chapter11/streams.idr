module Streams
-- section 11.1

import Data.Primitives.Views
import Data.Nat.Views

-- playing around with views and proofs --
test1 : Divides (the Int 32) (the Int 12)
test1 = 32 `divides` 12

test2 : Int -> Int
test2 x with (x `divides` 12)
  test2 ((12 * div) + rem) | (DivBy prf) = rem

test3 : Int.Divides ((12 * 3) + 6) (the Int 12)
test3 = Int.DivBy {rem = 6} {d = 12} {div = 3} Refl

-- infinite lists and the Stream type

data InfList : Type -> Type where
  (::) : (value : elem) -> Inf (InfList elem) -> InfList elem
%name InfList xs, ys, zs

total
countFrom : Integer -> InfList Integer
countFrom x = x :: countFrom (x + 1) -- the recursive call is implicitly wrapped in a Delay by Idris

total
getPrefix : (count : Nat) -> InfList a -> List a
getPrefix Z xs = []
getPrefix (S k) (x :: xs) = x :: getPrefix k xs

labelWith : Stream l -> List a -> List (l, a)
labelWith xs [] = []
labelWith (l :: ls) (x :: xs) = (l, x) :: labelWith ls xs

label : List a -> List (Integer, a)
label = labelWith (iterate (+ 1) 0)

quiz : Stream Int -> (score : Nat) -> IO ()
quiz (x :: y :: xs) score =
  do putStrLn ("Score so far: " ++ show score)
     putStrLn (show x ++ " * " ++ show y ++ "? ")
     answer <- getLine
     if (cast answer) == x * y
        then do putStrLn "Correct!"
                quiz xs (score + 1)
        else do putStrLn ("Wrong, the answer is " ++ show (x * y))
                quiz xs score
-- :exec quiz (arithInputs 12345) 0

-- simple random number generator
randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                   (seed' `shiftR` 2) :: randoms seed'

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound x with (divides x 12)
      bound ((12 * div) + rem) | (DivBy prf) = rem + 1



-- Exercises...
every_other : Stream a -> Stream a
every_other (_ :: x :: xs) = x :: every_other xs

Functor InfList where
  map f (x :: xs) = (f x) :: map f xs

ex_2 : List Integer
ex_2 = getPrefix 10 (map (*2) (countFrom 1))

data Face = Heads
          | Tails

total
coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips Z xs = []
coinFlips (S k) (x :: xs) = (getFace x) :: coinFlips k xs
  where
    getFace : Int -> Face
    getFace x with (x `divides` 2)
      getFace ((2 * div) + rem) | (DivBy prf) =
        case rem of
             1 => Heads
             _ => Tails

total
square_root_approx : (number : Double) -> (approx : Double) -> Stream Double
square_root_approx number approx =
  iterate (\x => (x + (number / x)) / 2)
          approx

total
square_root_bound : (max : Nat) -> (number : Double) -> (bound : Double) ->
                    (approxs : Stream Double) -> Double
square_root_bound Z _ _ (x :: xs) = x
square_root_bound (S k) number bound (x :: xs) =
  let difference = abs $ (x * x) - number in
      if difference < bound
      then x
      else square_root_bound k number bound xs

square_root : (number : Double) -> Double
square_root number =
  square_root_bound 100 number 0.00000001
                    (square_root_approx number number)


