module Section1

import System.Concurrency.Channels

%default total

data Message = Add Nat Nat

partial
adder : IO ()
adder = do Just sender_chan <- listen 1 | Nothing => adder
           Just msg <- unsafeRecv Message sender_chan | Nothing => adder
           case msg of
                Add k j => do ok <- unsafeSend sender_chan (k + j)
                              adder
           pure ()

partial
main : IO ()
main = do Just adder_id <- spawn adder | Nothing => putStrLn "spawn failed"
          Just chan <- connect adder_id | Nothing => putStrLn "connection failed"
          ok <- unsafeSend chan (Add 2 3)
          Just answer <- unsafeRecv Nat chan | Nothing => putStrLn "send failed"
          printLn answer
