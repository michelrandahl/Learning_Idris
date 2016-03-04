module Main

-- basic helloworld
main : IO()
main = putStrLn "hello type dependend world!"

-- what type should stuff be?
-- main = putStrLn ?stuff
-- check type in console with $ :t Main.stuff

-- how can we print a char?
-- main = putStrLn (?convert 'a')
-- check type in console with $ :t Main.convert
-- the function cast can perform the conversion for us
-- main = putStrLn (cast 'a')

StringOrInt : Bool -> Type
StringOrInt x = case x of
                     True => Int
                     False => String

getStringOrInt : (x : Bool) -> StringOrInt x
getStringOrInt x = case x of
                        True => 94
                        False => "Ninety four"

valToString : (x : Bool) -> StringOrInt x -> String
valToString x val = case x of
                         True => cast val
                         False => val
