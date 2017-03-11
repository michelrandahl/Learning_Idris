module hello_world

import Effects
import Effect.StdIO
import Data.Vect


vadd : Vect n Int -> Vect n Int -> Vect n Int
vadd [] [] = []
vadd (x::xs) (y::ys) = x+y :: vadd xs ys

hello : Eff () [STDIO]
hello = putStrLn "hello world"



main : IO ()
main = run hello
