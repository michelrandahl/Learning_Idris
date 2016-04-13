module Main

import System

printLength : IO ()
printLength = getLine >>= \input => let len = length input in
                                        putStrLn (show len)

maxOfStrings : IO ()
maxOfStrings = do
  x <- getLine
  y <- getLine
  let xLen = length x
  let yLen = length y
  let maxLen = max xLen yLen
  putStrLn (show maxLen)

maxOfStrings2 : IO ()
maxOfStrings2 =
  getLine >>= \x =>
  getLine >>= \y =>
              let
                xLen = length x
                yLen = length y
                maxLen = max xLen yLen
              in
                putStrLn (show maxLen)

readNumber : IO (Maybe Nat)
readNumber = do
  input <- getLine
  if all isDigit (unpack input) then
    pure (Just (cast input))
  else
    pure Nothing

readNumbers : IO (Maybe (Nat, Nat))
readNumbers = do
  Just num1 <- readNumber | Nothing => pure Nothing
  Just num2 <- readNumber | Nothing => pure Nothing
  pure (Just (num1, num2))

readPair : IO (String, String)
readPair = do str1 <- getLine
              str2 <- getLine
              pure (str1, str2)

usePair : IO ()
usePair = do (str1, str2) <- readPair
             putStrLn ("following were entered: " ++
                       str1 ++ " and " ++ str2)

countdown : (secs : Nat) -> IO ()
countdown Z = putStrLn "gooo!"
countdown (S secs) = do
  putStrLn (show (S secs))
  usleep 1000000
  countdown secs

-- this function isn't total because there is no guarantee of termination
countdowns : IO ()
countdowns = do
  putStr "enter starting number: "
  Just startNum <- readNumber | Nothing => do putStrLn "invalid"
                                              countdowns
  countdown startNum
  putStr "more countdown?(y/n)"
  yn <- getLine
  if yn == "y" then countdowns
               else pure ()


-- exercise 5.2.4
-- this function isn't total because there is no guarantee of termination
guess : (target : Nat) -> (guesses : Nat) -> IO ()
guess target guesses = do
  putStrLn ("guess the number! (attempt: " ++ (show guesses) ++ ")")
  Just user_guess <- readNumber | Nothing => do putStrLn "invalid"
                                                guess target guesses
  if user_guess == target then do
    putStrLn "correct!"
    pure ()
  else
    if user_guess < target then do
      putStrLn "too low"
      guess target (S guesses)
    else do
      putStrLn "too high"
      guess target (S guesses)

guess_number_game : IO ()
guess_number_game = do
  seed <- time
  let ran = mod seed 100
  guess (cast ran) 0

customReplWith : (state : a) ->
                 (prompt : String) ->
                 (onInput : a -> String -> Maybe (String, a)) ->
                 IO ()
customReplWith state prompt onInput = do
  putStrLn prompt
  input <- getLine
  case onInput state input of
       Nothing => pure ()
       Just (str, state') => do
         putStr str
         customReplWith state' prompt onInput

test : IO ()
test = customReplWith 0 "hello" (\x => \s => Just (s, (S x)))

customRepl : (prompt : String) ->
              (onInput : String -> String) ->
              IO ()
customRepl prompt onInput = do
  putStrLn prompt
  input <- getLine
  putStr (onInput input)
  customRepl prompt onInput

test2 : IO ()
test2 = customRepl "lala" (\s => "ok")




