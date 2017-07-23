module ArithCmd
-- section 11.3

import System
import Data.Primitives.Views

%default total

data Fuel = Dry | More (Lazy Fuel)

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String

data ConsoleIO : Type -> Type where
  Quit : action -> ConsoleIO action
  Do : Command action ->
               (action ->
               Inf (ConsoleIO next_action)) ->
               ConsoleIO next_action

(>>=) : Command action ->
               (action ->
               Inf (ConsoleIO next_action)) ->
               ConsoleIO next_action
(>>=) = Do

runCommand : Command action -> IO action
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine

run : Fuel -> ConsoleIO action -> IO (Maybe action)
run fuel (Quit action) = pure (Just action)
run Dry (Do action f) = pure Nothing
run (More fuel) (Do action f) =
  do res <- runCommand action
     run fuel (f res)

partial
forever : Fuel
forever = More forever

mutual
  correct : Stream Int -> (score : Nat) -> ConsoleIO Nat
  correct xs score = do PutStr "correct!\n"
                        quiz xs (score + 1)

  wrong : Stream Int -> (answer : Int) -> (score : Nat) -> ConsoleIO Nat
  wrong xs answer score =
    do PutStr ("wrong... answer is: " ++ show answer ++ "\n")
       quiz xs score

  quiz : Stream Int -> (score : Nat) -> ConsoleIO Nat
  quiz (x :: y :: xs) score =
    do PutStr ("Score so far: " ++ show score ++ "\n")
       PutStr (show x ++ " * " ++ show y ++ "? ")
       answer <- GetLine
       if toLower answer == "quit"
       then Quit score
       else if (cast answer == x * y)
            then correct xs score
            else wrong xs (x*y) score

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
          Just score <- run forever (quiz (arithInputs (fromInteger seed)) 0)
              | Nothing => putStrLn "out of fuel"
          putStrLn ("final score: " ++ show score)


