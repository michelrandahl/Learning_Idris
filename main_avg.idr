module Main

import Average

showAverage : String -> String
showAverage str =
  "The avg word length is: " ++
  show (average str) ++ "\n"

main : IO()
main =
  repl "Enter a string: "
       showAverage
