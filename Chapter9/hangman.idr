module Hangman

import Data.Vect

-- RECAP ON DEPENDENT PAIRS

-- naive attempt uses a custom data type
data VectUnknown : Type -> Type where
  MkVect : (len : Nat) -> Vect len a -> VectUnknown a

readVect : IO (len ** Vect len String)
readVect = do x <- getLine
              if (x == "")
              then pure (Z ** [])
              else do (n ** xs) <- readVect
                      pure ((S n) ** x :: xs)

-- HANGMAN

removeElem : (value : a) ->
             (xs : Vect (S n) a) ->
             (prf : Elem value xs) ->
             Vect n a
removeElem value (value :: ys) Here = ys
removeElem {n = Z} value (y :: []) (There later) = absurd later
removeElem {n = (S k)} value (y :: ys) (There later) =
  y :: removeElem value ys later

removeElem_auto : (value : a) ->
                  (xs : Vect (S n) a) ->
                  {auto prf : Elem value xs} ->
                  Vect n a
removeElem_auto value xs {prf} = removeElem value xs prf

data WordState : (guesses_remaining : Nat) -> (letters : Nat) -> Type where
  MkWordState : (word : String) -> (missing : Vect letters Char) -> WordState guesses_remaining letters

data Finished : Type where
  Lost : (game : WordState 0 (S letters)) -> Finished
  Won  : (game : WordState (S guesses) 0) -> Finished

data ValidInput : List Char -> Type where
  Letter : (c : Char) -> ValidInput [c]

isValidNil : ValidInput [] -> Void
isValidNil (Letter _) impossible

isValidMany : ValidInput (x :: x' :: xs) -> Void
isValidMany (Letter _) impossible

isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [] = No isValidNil
isValidInput [x] = Yes (Letter x)
isValidInput (x :: x' :: xs) = No isValidMany

isValidString : (s : String) -> Dec (ValidInput (unpack s))
isValidString s = isValidInput (unpack s)

readGuess : IO (x ** ValidInput x)
readGuess = do putStr "Guess:"
               x <- getLine
               case isValidString (toUpper x) of
                    Yes prf => pure (_ ** prf)
                    No contra => do putStrLn "Invalid guess"
                                    readGuess

processGuess : (letter : Char) ->
               WordState (S guesses) (S letters) ->
               Either (WordState guesses (S letters))
                      (WordState (S guesses) letters)
processGuess letter (MkWordState word missing) =
  case isElem letter missing of
       Yes prf =>
         let missing' = removeElem letter missing prf in
           Right (MkWordState word missing')
       No contra => Left (MkWordState word missing)

game : WordState (S guesses) (S letters) -> IO Finished
game {guesses} {letters} state =
  do (_ ** Letter guess) <- readGuess
     case processGuess guess state of
          Left l => do putStrLn "Wrong!! :("
                       case guesses of
                            Z   => pure (Lost l)
                            S k => game l
          Right r => do putStrLn "Right!"
                        case letters of
                             Z   => pure (Won r)
                             S k => game r

main : IO ()
main = do let word = "test"
          let state  = MkWordState word $ fromList $ unpack $ toUpper word
          result <- game {guesses = length word} state
          case result of
               Lost game => putStrLn "You loose"
               Won game => putStrLn "You Win!"



