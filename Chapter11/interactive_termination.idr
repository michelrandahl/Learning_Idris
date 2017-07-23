module Interactive_termination
-- section 11.3

%default total

data InfIO : Type where
  Do : IO action -> (action -> Inf InfIO) -> InfIO

(>>=) : IO action -> (action -> Inf InfIO) -> InfIO
(>>=) = Do

greet : InfIO
greet = do putStr "enter your name: "
           name <- getLine
           putStrLn ("hello" ++ name)
           greet

