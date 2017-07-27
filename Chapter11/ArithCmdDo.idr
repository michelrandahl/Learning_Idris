module ArithCmdDo

-- section 11.3 with exercises

import Data.Primitives.Views
import System

%default total

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                   (seed' `shiftR` 2) :: randoms seed'

boundedInputs : (seed : Int ) -> Stream Int
boundedInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound x with (x `divides` 12)
      bound ((12 * div) + rem) | (DivBy prf) = rem + 1

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String

  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleIODo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

data Input = Answer Int
           | QuitCmd

readInput : (prompt : String) -> Command Input
readInput prompt = do PutStr prompt
                      answer <- GetLine
                      if toLower answer == "quit"
                         then Pure QuitCmd
                         else Pure $ Answer $ cast answer

mutual
  correct : Stream Int -> (num_questions : Nat) -> (score : Nat) -> ConsoleIO Nat
  correct xs num_questions score =
    do PutStr "correct\n"
       quiz xs num_questions (S score)

  wrong : Stream Int -> (correct : Int) -> (num_questions : Nat) -> (score : Nat) -> ConsoleIO Nat
  wrong xs result num_questions score =
    do PutStr $ "wrong, the answer is " ++ show result ++ "\n"
       quiz xs num_questions score

  quiz : Stream Int -> (num_questions : Nat) -> (score : Nat) -> ConsoleIO Nat
  quiz (x :: y :: xs) num_questions score =
    do let score_status = show score ++ " / " ++ show num_questions
       PutStr $ "score so far: " ++ score_status ++ "\n"
       let question = show x ++ " * " ++ show y ++ "? "
       input <- readInput question
       let result = x * y
       case input of
            Answer a => if a == result
                           then correct xs (S num_questions) score
                           else wrong xs result (S num_questions) score
            QuitCmd => Quit score

runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand (Pure x) = pure x
runCommand (Bind a f) = do res <- runCommand a
                           runCommand $ f res

data Fuel = Dry
          | More (Lazy Fuel)

run : Fuel -> ConsoleIO a -> IO (Maybe a)
run _ (Quit x) = pure (Just x)
run Dry _ = pure Nothing
run (More fuel) (Do a f) = do res <- runCommand a
                              run fuel $ f res

partial
forever : Fuel
forever = More forever

partial
main : IO ()
main = do seed <- time
          let xs = boundedInputs (fromInteger seed)
          Just score <- run forever $ quiz xs Z Z
                     | Nothing => putStrLn "out of fuel.."
          putStrLn $ "final score: " ++ show score


