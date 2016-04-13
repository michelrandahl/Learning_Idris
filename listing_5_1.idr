module Main

main : IO()
main = do
  putStr "enter name: "
  x <- getLine
  putStrLn ("hello " ++ x ++ "!")

