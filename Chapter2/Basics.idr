module Basics
{-
 module declaration is optionally,
 -but will default to Main if not specified
-}


||| Calculate the avg length of words in a string/
||| @str a string containing words separated by whitespace.
export -- export will expose the following function to other modules which imports this module
average : (str : String) -> Double
average str = let numWords = wordCount str
                  totalLength = sum (allLengths (words str)) in
                  cast totalLength / cast numWords
  where
    wordCount : String -> Nat
    wordCount str = length (words str)

    allLengths : List String -> List Nat
    allLengths xs = map length xs

showAverage : String -> String
showAverage str = "The Avg word length is: " ++
                  show (average str) ++ "\n"

main : IO ()
main = repl "Enter a string: " showAverage


-- casting types
myinteger : Integer
myinteger = 42
mydouble : Double
mydouble = 1.333

myresult : Double
myresult = cast myinteger + mydouble

myresult2 : Double
myresult2 = the Double (cast (myinteger + cast mydouble))

double : Num ty => ty -> ty
double x = x * x

somewords : List String
somewords = words "hello world"

somestring : String
somestring = unwords ["hello", "world"]



