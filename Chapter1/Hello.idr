module Main

StringOrInt : Bool -> Type
StringOrInt True = Int
StringOrInt False = String

getStringOrInt : (x : Bool) -> StringOrInt x
getStringOrInt False = "Ninety four"
getStringOrInt True = 94

valToString : (x : Bool) -> StringOrInt x -> String
valToString False val = val
valToString True val = cast val

main : IO ()
main = putStrLn (cast 'x')
