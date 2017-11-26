module Section2_1

import System.Concurrency.Channels

%default total

data MessagePID : (iface : reqType -> Type) -> Type where
  MkMessage : PID -> MessagePID iface

data Message = Add Nat Nat

AdderType : Message -> Type
AdderType (Add x y) = Nat

data ListAction : Type where
  Length : List elem -> ListAction
  Append : List elem -> List elem -> ListAction

ListType : ListAction -> Type
ListType (Length xs) = Nat
ListType (Append {elem} xs ys) = List elem

data ProcState = NoRequest | Sent | Complete

data Process : (iface : reqType -> Type) -> (retType : Type) -> (in_state : ProcState) -> (out_state : ProcState) -> Type where
  Action : IO a -> Process iface a st st
  Pure : a -> Process iface a st st
  Spawn : Process service_iface () NoRequest Complete -> Process iface (Maybe (MessagePID service_iface)) st st
  Request : MessagePID service_iface -> (msg : service_reqType) -> Process iface (service_iface msg) st st
  Respond : ((msg : reqType) -> Process iface (iface msg) NoRequest NoRequest) -> Process iface (Maybe reqType) st Sent
  Loop : Inf (Process iface a NoRequest Complete) -> Process iface a Sent Complete
  (>>=) : Process iface a st1 st2 -> (a -> Process iface b st2 st3) -> Process iface b st1 st3

Service : (iface : reqType -> Type) -> Type -> Type
Service iface retType = Process iface retType NoRequest Complete

NoRecv : Void -> Type
NoRecv = const Void

Client : Type -> Type
Client retType = Process NoRecv retType NoRequest NoRequest

procAdder : Service AdderType ()
procAdder = do Respond (\msg => case msg of Add x y => Pure $ x + y)
               Loop procAdder
{-
understanding procAdder:
Process (a = ?_) (st1 = ?st1) (st2 = Sent) >>= (\_ => Process () st2 (st3 = Complete)) : Process () (st1 = NoRequest) st3
we don't care what a is as he is discarded into the trash-underscore in the lambda fun.
we don't know what st1 is immediatly, but can infer it from the resulting type in the end.
'Loop procAdder' creates the type 'Process () Sent Complete', and thus we make sure (st2 == Sent), we set (st3 = Complete) and (b = ())
-}

procList : Service ListType ()
procList = do Respond (\msg => (case msg of
                                     (Length xs) => Pure $ length xs
                                     (Append xs ys) => Pure $ xs ++ ys))
              Loop procList

procMain : Client ()
procMain = do Just adder_id <- Spawn procAdder | _ => Action (putStrLn "spawn failed")
              answer <- Request adder_id $ Add 2 3
              Action $ printLn answer
{-
Process (a = pid) (st1 = ?st_init) (st2 = ?st_init)
>>= (\adder_id => Process (b = x) st2 (st3 = ?st_intermed)
>>= (\b => Process (c = ()) (st1 = ?st_init) (st4 = ?st_init) : Process (c == ()) (st1 = NoRequest) (st4 = NoRequest)
-}

procMain2 : Client ()
procMain2 = do Just list_process <- Spawn procList | _ => Action (putStrLn "spawn failed")
               len <- Request list_process (Length [1,2,3])
               Action $ printLn len

               xs <- Request list_process (Append [1,2,3] [4,5,6])
               Action $ printLn xs

data Fuel = Dry | More (Lazy Fuel)

run : Fuel -> Process iface t in_state out_state -> IO (Maybe t)
run fuel (Request {service_iface} (MkMessage pid) msg) =
  do Just chan <- connect pid | _ => pure Nothing
     ok <- unsafeSend chan msg
     if ok
     then do Just x <- unsafeRecv (service_iface msg) chan | _ => pure Nothing
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
run fuel (Respond {reqType} calc) =
  do Just sender <- listen 1 | _ => (pure $ Just $ Nothing)
     Just msg <- unsafeRecv reqType sender | _ => (pure $ Just $ Nothing)
     Just res <- run fuel $ calc msg | _ => pure Nothing
     unsafeSend sender res
     pure $ Just $ Just msg

partial
forever : Fuel
forever = More forever

partial
runProc : Process iface () in_state out_state -> IO ()
runProc proc = do run forever proc
                  pure ()

