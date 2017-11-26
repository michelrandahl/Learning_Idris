module ProcessLib

import System.Concurrency.Channels

%default total

export
data MessagePID : (iface : reqType -> Type) -> Type where
  MkMessage : PID -> MessagePID iface

public export
data ProcState = NoRequest | Sent | Complete

public export
data Process : (iface : reqType -> Type) -> Type -> (in_state : ProcState) -> (out_state : ProcState) -> Type where
  Action : IO a -> Process iface a st st
  Pure : a -> Process iface a st st
  Spawn : Process service_iface () NoRequest Complete -> Process iface (Maybe (MessagePID service_iface)) st st
  Request : MessagePID service_iface -> (msg : service_reqType) -> Process iface (service_iface msg) st st
  Respond : ((msg : reqType) -> Process iface (iface msg) NoRequest NoRequest) -> Process iface (Maybe reqType) st Sent
  Loop : Inf (Process iface a NoRequest Complete) -> Process iface a Sent Complete
  (>>=) : Process iface a st1 st2 -> (a -> Process iface b st2 st3) -> Process iface b st1 st3

public export
data Fuel = Dry | More (Lazy Fuel)

export partial
forever : Fuel
forever = More forever

export
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

public export
NoRecv : Void -> Type
NoRecv = const Void

public export
Service : (iface : reqType -> Type) -> Type -> Type
Service iface retType = Process iface retType NoRequest Complete

public export
Client : Type -> Type
Client retType = Process NoRecv retType NoRequest NoRequest

export partial
runProc : Process iface () in_state out_state -> IO ()
runProc proc = do run forever proc
                  pure ()
