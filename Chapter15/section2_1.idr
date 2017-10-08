module Section2_1

import System.Concurrency.Channels

%default total

data MessagePID = MkMessage PID

data Message = Add Nat Nat

data ProcState = NoRequest | Sent | Complete

data Process : Type -> (in_state : ProcState) -> (out_state : ProcState) -> Type where
  Action : IO a -> Process a st st
  Pure : a -> Process a st st
  Spawn : Process () NoRequest Complete -> Process (Maybe MessagePID) st st
  Request : MessagePID -> Message -> Process Nat st st
  Respond : ((msg : Message) -> Process Nat NoRequest NoRequest) -> Process (Maybe Message) st Sent
  Loop : Inf (Process a NoRequest Complete) -> Process a Sent Complete
  (>>=) : Process a st1 st2 -> (a -> Process b st2 st3) -> Process b st1 st3

-- Service
procAdder : Process () NoRequest Complete
procAdder = do Respond (\msg => case msg of Add x y => Pure $ x + y)
               Loop procAdder
{-
understanding procAdder:
Process (a = ?_) (st1 = ?st1) (st2 = Sent) >>= (\_ => Process () st2 (st3 = Complete)) : Process (st1 = NoRequest) st3
we don't care what a is as he is discarded into the trash-underscore in the lambda fun.
we don't know what st1 is immediatly, but can infer it from the resulting type in the end.
'Loop procAdder' creates the type 'Process () Sent Complete', and thus we make sure (st2 == Sent), we set (st3 = Complete) and (b = ())
-}

-- Client
procMain : Process () NoRequest NoRequest
procMain = do Just adder_id <- Spawn procAdder | _ => Action (putStrLn "spawn failed")
              answer <- Request adder_id $ Add 2 3
              Action $ printLn answer
{-
Process (a = pid) (st1 = ?st_init) (st2 = ?st_init)
>>= (\adder_id => Process (b = x) st2 (st3 = ?st_intermed)
>>= (\b => Process (c = ()) (st1 = ?st_init) (st4 = ?st_init) : Process (c == ()) (st1 = NoRequest) (st4 = NoRequest)
-}

data Fuel = Dry | More (Lazy Fuel)

run : Fuel -> Process t in_state out_state -> IO (Maybe t)
run fuel (Request (MkMessage pid) msg) =
  do Just chan <- connect pid | _ => pure Nothing
     ok <- unsafeSend chan msg
     if ok
     then do Just x <- unsafeRecv Nat chan | _ => pure Nothing
             pure (Just x)
     else pure Nothing
run Dry _ = pure Nothing
run fuel (Action action) = do res <- action
                              pure $ Just res
run fuel (Pure x) = pure $ Just x
run fuel (action >>= next) =
  do Just x <- run fuel action | _ => pure Nothing
     run fuel $ next x
run (More fuel) (Loop act) = run fuel act
run fuel (Spawn proc) =
  do Just pid <- spawn (do run fuel proc; pure ()) | _ => pure Nothing
     pure $ Just $ Just $ MkMessage pid
run fuel (Respond calc) =
  do Just sender <- listen 1 | _ => (pure $ Just $ Nothing)
     Just msg <- unsafeRecv Message sender | _ => (pure $ Just $ Nothing)
     Just res <- run fuel $ calc msg | _ => pure Nothing
     unsafeSend sender res
     pure $ Just $ Just msg

partial
forever : Fuel
forever = More forever

partial
runProc : Process () in_state out_state -> IO ()
runProc proc = do run forever proc
                  pure ()

