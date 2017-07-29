module Section3

-- section3 of chapter 12, with exercises

import System
import Data.Primitives.Views

%default total

record Score where
  constructor MkScore
  correct : Nat
  attempted : Nat

record GameState where
  constructor MkGameState
  score : Score
  difficulty : Int

Show GameState where
  show game_state =
    (show $ correct   $ score game_state) ++ "/" ++
    (show $ attempted $ score game_state) ++ "\n" ++
    "Difficulty: " ++ (show $ difficulty game_state)

addWrong : GameState -> GameState
addWrong = record { score->attempted $= (+ 1) }

addCorrect : GameState -> GameState
addCorrect = record { score->correct $= (+ 1)
                    , score->attempted $= (+ 1) }

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String

  GetRandom : Command Int
  GetGameState : Command GameState
  PutGameState : GameState -> Command ()

  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

-- exercise 2
mutual
  Functor Command where
    map func x = x >>= pure . func

  Applicative Command where
    pure = Pure
    (<*>) f a = do f' <- f
                   a' <- a
                   pure $ f' a'

  Monad Command where
    (>>=) = Bind

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

data Input = Answer Int
           | QuitCmd

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

runCommand : (randoms : Stream Int) ->
             (state : GameState) ->
             (cmd : Command a) ->
             IO (a, Stream Int, GameState)
runCommand randoms state (PutStr x) = do putStr x
                                         pure ((), randoms, state)
runCommand randoms state GetLine = do str <- getLine
                                      pure (str, randoms, state)
runCommand (x :: randoms) state GetRandom =
  pure (getBounded x $ difficulty state, randoms, state)
  where
    getBounded : (val : Int) -> (max : Int) -> Int
    getBounded val max with (val `divides` max)
      getBounded val 0 | DivByZero = 1
      getBounded ((max * div) + rem) max | (DivBy prf) = abs rem + 1
runCommand randoms state GetGameState = pure (state, randoms, state)
runCommand randoms state (PutGameState new_state) = pure ((), randoms, new_state)
runCommand randoms state (Pure x) = pure (x, randoms, state)
runCommand randoms state (Bind c f) =
  do (x, new_randoms, new_state) <- runCommand randoms state c
     runCommand new_randoms new_state $ f x

run : Fuel ->
      (randoms : Stream Int) ->
      (state : GameState) ->
      (console_cmd : ConsoleIO a) ->
      IO (Maybe a, Stream Int, GameState)
run Dry randoms state _ = pure (Nothing, randoms, state)
run _ randoms state (Quit x) = pure (Just x, randoms, state)
run (More fuel) randoms state (Do c f) =
  do (x, new_randoms, new_state) <- runCommand randoms state c
     run fuel new_randoms new_state $ f x

--exercise 1
updateGameState : (GameState -> GameState) -> Command ()
updateGameState f = GetGameState >>= PutGameState . f

mutual
  -- exercise 1
  correct : ConsoleIO GameState
  correct = do PutStr "correct!\n"
               updateGameState addCorrect
               quiz

  -- exercise 1
  wrong : (expected : Int) -> ConsoleIO GameState
  wrong expected =
    do PutStr $ "wrong, the answer is " ++ show expected ++ "\n"
       updateGameState addWrong
       quiz

  readInput : (prompt : String) -> Command Input
  readInput prompt =
    do PutStr prompt
       answer <- GetLine
       -- note that if we input some garbage, it will return (Answer 0) because of cast
       -- $ the Int (cast "foobar")
       -- > 0
       if toLower answer == "quit"
          then Pure QuitCmd
          else Pure $ Answer $ cast answer

  quiz : ConsoleIO GameState
  quiz = do x <- GetRandom
            y <- GetRandom
            state <- GetGameState
            PutStr $ show state ++ "\n"
            input <- readInput $ show x ++ " * " ++ show y ++ "? "
            case input of
                 Answer answer => let expected = x * y in
                                      if answer == expected
                                         then correct
                                         else wrong expected
                 QuitCmd => Quit state

randoms : (seed : Int) -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                   (seed' `shiftR` 2) :: randoms seed'

initState : GameState
initState = MkGameState (MkScore 0 0) 12

partial
main : IO ()
main = do seed <- time
          let rands = randoms (fromInteger seed)
          (Just score, _, state) <-
            run forever rands initState quiz
            | _ => putStrLn "out of fuel..."
          putStrLn $ "final score: " ++ show state


-- EXERCISES --

-- EXERCISE 1
-- updateGameState, correct, wrong

-- EXERCISE 2
-- Functor, Applicative, Monad for Command

-- EXERCISE 3-4

record Votes where
  constructor MkVotes
  upvotes : Integer
  downvotes : Integer

record Article where
  constructor MkArticle
  title : String
  url : String
  score : Votes

initPage : (title : String) -> (url : String) -> Article
initPage title url = MkArticle title url (MkVotes 0 0)

getScore : Article -> Integer
getScore a = let score' = score a in
                 upvotes score' - downvotes score'

badSite : Article
badSite = MkArticle "bad page" "http://bad.com" (MkVotes 5 47)

goodSite : Article
goodSite = MkArticle "good page" "http://good.com" (MkVotes 101 7)

addUpvote : Article -> Article
addUpvote = record { score->upvotes $= (+ 1) }

addDownvote : Article -> Article
addDownvote = record { score->downvotes $= (+ 1) }

