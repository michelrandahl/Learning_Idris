module Section3

import Data.Vect

%default total

data GameState : Type where
  NotRunning : GameState
  Running : (guesses : Nat) -> (letters : Nat) -> GameState

letters : String -> List Char
letters s = nub $ map toUpper $ unpack s

data GuessResult = Correct | InCorrect

data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
  NewGame : (word : String) ->
            GameCmd () NotRunning (const (Running 6 $ length $ letters word))
  Won : GameCmd () (Running (S guesses) 0) (const NotRunning)
  Lost : GameCmd () (Running 0 (S guesses)) (const NotRunning)
  Guess : (c : Char) -> GameCmd GuessResult (Running (S guesses) (S letters))
          (\res => (case res of
                         Correct => Running (S guesses) letters
                         InCorrect => Running guesses (S letters)))

  ShowState : GameCmd () state (const state)
  Message : String -> GameCmd () state (const state)
  ReadGuess : GameCmd Char state (const state)

  Pure : (res : ty) -> GameCmd ty (state_fn res) state_fn
  (>>=) : GameCmd a state1 state2_fn ->
          ((res : a) -> GameCmd b (state2_fn res) state3_fn) ->
          GameCmd b state1 state3_fn

namespace Loop
  data GameLoop : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
    (>>=) : GameCmd a state1 state2_fn ->
            ((res : a) -> Inf (GameLoop b (state2_fn res) state3_fn)) ->
            GameLoop b state1 state3_fn
    Exit : GameLoop () NotRunning (const NotRunning)

gameLoop : GameLoop () (Running (S guesses) (S letters)) (const NotRunning)
gameLoop {guesses} {letters} = do
  ShowState
  g <- ReadGuess
  ok <- Guess g
  case ok of
       Correct => case letters of
                       Z => do Won; ShowState; Exit
                       (S k) => do Message "correct!"; gameLoop
       InCorrect => case guesses of
                         Z => do Lost; ShowState; Exit
                         (S k) => do Message "incorrect"; gameLoop

hangman : GameLoop () NotRunning (const NotRunning)
hangman = do NewGame "testing"
             gameLoop

data Game : GameState -> Type where
  GameStart : Game NotRunning
  GameWon : (word : String) -> Game NotRunning
  GameLost : (word : String) -> Game NotRunning
  InProgress : (word : String) -> (guesses : Nat) ->
               (missing : Vect letters Char) ->
               Game (Running guesses letters)

Show (Game g) where
  show GameStart = "starting..."
  show (GameWon word) = "game won: word was " ++ word
  show (GameLost word) = "game lost: word was " ++ word
  show (InProgress word guesses missing) =
    "\n" ++ (pack $ map hideMissing $ unpack word) ++
    "\n" ++ show guesses ++ " guesses left"
    where
      hideMissing : Char -> Char
      hideMissing c = if c `elem` missing then '-' else c

data Fuel = Dry | More (Lazy Fuel)

-- game either runs dry or continues with OK
data GameResult : (ty : Type) -> (ty -> GameState) -> Type where
  OK : (res : ty) -> Game (outstate_fn res) -> GameResult ty outstate_fn
  OutOfFuel : GameResult ty outstate_fn

ok : (res : ty) -> Game (outstate_fn res) -> IO (GameResult ty outstate_fn)
ok res state = pure $ OK res state

removeElem : (x : a) -> (xs : Vect (S n) a) ->
             {auto proof' : Elem x xs} ->
             Vect n a
removeElem x (x :: xs) {proof' = Here} = xs
removeElem {n = Z} x (y :: []) {proof' = There later} = absurd later
removeElem {n = (S k)} x (y :: xs) {proof' = There later} =
  y :: removeElem x xs

runCmd : Fuel -> Game instate -> GameCmd ty instate outstate_fn ->
         IO (GameResult ty outstate_fn)
runCmd fuel state (NewGame word) =
  let word_vector = fromList $ letters word in
    ok () (InProgress (toUpper word) _ word_vector)
runCmd fuel (InProgress word _ _) Won =
  ok () (GameWon word)
runCmd fuel (InProgress word _ _) Lost =
  ok () (GameLost word)
runCmd fuel (InProgress word (S guesses) missing) (Guess c) =
  case isElem c missing of
       Yes prf => ok Correct $ InProgress word (S guesses) (removeElem c missing)
       No contra => ok InCorrect $ InProgress word guesses missing
runCmd fuel state ShowState =
  do printLn state; ok () state
runCmd fuel state (Message msg) =
  do printLn msg; ok () state
runCmd (More fuel) state ReadGuess = do
  putStr "Guess: "
  input <- getLine
  case unpack input of
       [x] => if isAlpha x
                 then ok (toUpper x) state
                 else do putStrLn "invalid input"
                         runCmd fuel state ReadGuess
       _ => do putStrLn "invalid input"
               runCmd fuel state ReadGuess
runCmd fuel state (Pure res) = ok res state
runCmd fuel state (cmd >>= next) = do
  OK res new_state <- runCmd fuel state cmd | OutOfFuel => pure OutOfFuel
  runCmd fuel new_state (next res)
runCmd Dry _ _ = pure OutOfFuel

run : Fuel ->
      Game instate ->
      GameLoop ty instate outstate_fn ->
      IO (GameResult ty outstate_fn)
run Dry _ _ = pure OutOfFuel
run (More fuel) state (cmd >>= next) = do
  OK res new_state <- runCmd fuel state cmd | OutOfFuel => pure OutOfFuel
  run fuel new_state (next res)
run (More fuel) state Exit = ok () state

partial
forever : Fuel
forever = More forever

partial
main : IO ()
main = do run forever GameStart hangman
          pure ()


