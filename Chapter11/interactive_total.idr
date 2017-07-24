module Interactive_total
-- section 11.2

import Data.Primitives.Views
import System

-- totality checks for everybody in da club (exept those poor functions marked as partial)
%default total

data InfIO : Type where
  Do : IO action -> (action -> Inf InfIO) -> InfIO

(>>=) : IO action -> (action -> Inf InfIO) -> InfIO
(>>=) = Do

loopPrint : String -> InfIO
loopPrint msg =
  do putStrLn msg
     loopPrint msg

partial -- Idris wrongly reports run1 to be total (must be a bug..?)
run1 : InfIO -> IO ()
run1 (Do action cont) = do res <- action
                           run1 (cont res)
-- following runs forever... forever eva!?..
-- :exec run1 (loopPrint "on and on...")
-- see idris I told you so, it aint total!..

data Fuel = Dry | More Fuel

tank : Nat -> Fuel
tank Z = Dry
tank (S k) = More (tank k)

run : Fuel -> InfIO -> IO ()
run Dry _ = putStrLn "out of fuel.."
run (More fuel) (Do action f) = do res <- action
                                   run fuel (f res)

data LazyFuel = LazyDry | LazyMore (Lazy LazyFuel)

-- this fella aint total because Idris expects Lazy type stuff to be reduced, whereas it doesn't require that from Inf type stuff
partial
forever : LazyFuel
forever = LazyMore forever

run2 : LazyFuel -> InfIO -> IO ()
run2 LazyDry _ = putStrLn "out of fuel"
run2 (LazyMore fuel) (Do io_action f) =
  do res <- io_action
     run2 fuel (f res)
-- run2 is total because it reduces on its fuel
-- however, we can run it forever with the 'forever' fuel
-- :exec run2 forever (loopPrint "on and on again...")

quiz : Stream Int -> (score : Nat) -> InfIO
quiz (x :: y :: xs) score =
  do putStrLn ("score so far: " ++ show score)
     putStr (show x ++ " * " ++ show y)
     answer <- getLine
     if (cast answer == x * y)
     then do putStrLn "correct!"
             quiz xs (score + 1)
     else do putStrLn ("wrong!, the answer is " ++ show (x * y))
             quiz xs score

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                   (seed' `shiftR` 2) :: randoms seed'

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound x with (divides x 12)
      bound ((12 * div) + rem) | (DivBy prf) = abs rem + 1

partial
main : IO ()
main = do seed <- time
          run2 forever (quiz (arithInputs (fromInteger seed)) 0)

-- exercises
totalRepl : (prompt : String) -> (action : String -> String) -> InfIO
totalRepl prompt action = do putStrLn prompt
                             user_input <- getLine
                             putStrLn (action user_input)
                             totalRepl prompt action



