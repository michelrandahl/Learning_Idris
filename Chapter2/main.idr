module Main

import Basics

showAverage : String -> String
showAverage x = "The avg word len in: " ++
                show (average x) ++ "\n"

main : IO ()
main = repl "Enter a string..." showAverage
