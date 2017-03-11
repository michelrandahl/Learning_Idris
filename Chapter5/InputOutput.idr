module InputOutput

import System
import Data.Vect

main : IO ()
main =
  do putStr "Enter your name: "
     x <- getLine
     putStrLn ("hello " ++ x ++ "!")

printLength : IO ()
printLength = getLine >>= \input => let len = length input in
                                        putStrLn (show len)

printLength2 : IO ()
printLength2 =
  do putStr "input something: "
     input <- getLine
     let len = length input
     putStrLn (show len)

readNumber : IO (Maybe Nat)
readNumber =
  do input <- getLine
     if all isDigit (unpack input)
     then pure (Just (cast input))
     else pure Nothing

readNumbers : IO (Maybe (Nat, Nat))
readNumbers =
  do Just num1 <- readNumber | Nothing => pure Nothing
     Just num2 <- readNumber | Nothing => pure Nothing
     pure (Just (num1, num2))

countdown : (secs : Nat) -> IO ()
countdown Z = putStrLn "lift off!"
countdown (S secs) =
  do putStrLn (show (S secs))
     usleep 1000000
     countdown secs

readVectLen : (len : Nat) -> IO (Vect len String)
readVectLen Z = pure []
readVectLen (S k) =
  do x <- getLine
     xs <- readVectLen k
     pure (x :: xs)

data VectUnkown : Type -> Type where
  MkVect : (len : Nat) -> Vect len a -> VectUnkown a

readVect : IO (VectUnkown String)
readVect =
  do x <- getLine
     if (x == "")
     then pure (MkVect _ [])
     else do MkVect _ xs <-readVect
             pure (MkVect _ (x :: xs))

printVect : Show a => VectUnkown a -> IO ()
printVect (MkVect len xs) =
  putStrLn (show xs ++ " (length " ++ show len ++ ")")

readVect2 : IO (len ** Vect len String)
readVect2 =
  do x <- getLine
     if (x == "")
     then pure (_ ** [])
     else do (_ ** xs) <- readVect2
             pure (_ ** x :: xs)

zipInputs : IO ()
zipInputs =
  do putStrLn "enter first vector: "
     (len1 ** vec1) <- readVect2
     putStrLn "enter second vector: "
     (len2 ** vec2) <- readVect2
     case exactLength len1 vec2 of
          Nothing => putStrLn "diff lengths"
          Just vec2' => printLn (zip vec1 vec2')

