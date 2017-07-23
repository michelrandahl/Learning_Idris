module ArithCmdDo
-- section 11.3

import System
import Data.Primitives.Views

%default total

data Input = Answer Int
           | QuitCmd

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String

  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

-- namespace helps idris to avoid clash between bind functions with same name
namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

data ConsoleIO : Type -> Type where
  Quit : action -> ConsoleIO action
  Do : Command action ->
               (action ->
               Inf (ConsoleIO next_action)) ->
               ConsoleIO next_action

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand (Pure x) = pure x
runCommand (Bind x f) = do res <- runCommand x
                           runCommand (f res)

readInput : (prompt : String) -> Command Input
readInput prompt = do PutStr prompt
                      answer <- GetLine
                      if toLower answer == "quit"
                      then Pure QuitCmd
                      else Pure (Answer (cast answer))

mutual
  quiz : Stream Int -> (score : Nat) -> ConsoleIO Nat
  quiz (x :: y :: xs) score =
    do PutStr ("score so far: " ++ show score ++ "\n")
       input <- readInput (show x ++ " * " ++ show y ++ "? ")
       case input of
            Answer => if answer == x * y
                      then correct xs score
            QuitCmd => ?bar



