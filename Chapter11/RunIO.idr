module RunIO
-- section 11.3
%default total

data RunIO : Type -> Type where
  Quit : action -> RunIO action
  Do : IO action -> (action -> Inf (RunIO next_action)) -> RunIO next_action

(>>=) : IO action -> (action -> Inf (RunIO next_action)) -> RunIO next_action
(>>=) = Do

greet : RunIO ()
greet = do putStr "enter your name: "
           name <- getLine
           if name == ""
           then do putStrLn "bye..."
                   Quit ()
           else do putStrLn ("hello " ++ name)
                   greet

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

run : Fuel -> RunIO action_res -> IO (Maybe action_res)
run fuel (Quit action) = pure (Just action)
run Dry (Do z f) = pure Nothing
run (More fuel) (Do action f) =
  do res <- action
     run fuel (f res)

partial
main : IO ()
main = do run forever greet
          pure ()

