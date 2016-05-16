module Main

import System
import Data.Vect

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

read_vect_len : (len : Nat) -> IO (Vect len String)
read_vect_len Z = pure []
read_vect_len (S k) = do
  x <- getLine
  xs <- read_vect_len k
  pure (x :: xs)

data VectUnkown : Type -> Type where
  MkVect : (len : Nat) -> Vect len a -> VectUnkown a

read_vect : IO (VectUnkown String)
read_vect = do
  x <- getLine
  if (x == "") then
    pure (MkVect _ [])
  else do
    MkVect _ xs <- read_vect
    pure (MkVect _ (x :: xs))

printVect : Show a => VectUnkown a -> IO ()
printVect (MkVect len xs) =
  putStrLn (show xs ++ " (length " ++ show len ++ ")")

anyVect : (n ** Vect n String)
anyVect = (3 ** ?hole)


read_vect2 : IO (len ** Vect len String)
read_vect2 = do
  x <- getLine
  if (x == "") then
    pure (_ ** [])
  else do
    (_ ** xs) <- read_vect2
    pure (_ ** x :: xs)

zipInputs : IO ()
zipInputs = do
  putStrLn "Enter first vector and then a blank"
  (len1 ** vec1) <- read_vect2
  putStrLn "Enter second vector and then a blank"
  (len2 ** vec2) <- read_vect2
  case exactLength len1 vec2 of
       Nothing => putStrLn "vectors have different lengths"
       Just vec2' => printLn (zip vec1 vec2')


readToBlank : IO (List String)
readToBlank = do
  line <- getLine
  if (line == "") then
    pure []
  else do
    xs <- readToBlank
    pure (line :: xs)

readAndSave : IO ()
readAndSave = do
  putStrLn "enter list values"
  xs <- readToBlank
  putStrLn "enter file name"
  out_file <- getLine
  res <- writeFile out_file (unlines xs) -- TODO: error handling to make fun total
  case res of
       Right _ => putStrLn "file saved"
       Left err => putStrLn (show err)

readLines : (file : File) -> IO (len ** Vect len String)
readLines file = do
  eof <- fEOF file
  if eof then
    pure (_ ** [])
  else do
    Right line <- fGetLine file
    (_ ** lines) <- readLines file
    pure (_ ** line :: lines)

readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile filename = do
  Right f <- openFile filename Read | Left err => pure (_ ** [])
  readLines f




