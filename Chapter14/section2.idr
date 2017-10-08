module Section2

import Data.Vect

PIN : Type
PIN = Vect 4 Char

data ATMState = Ready | CardInserted | Session

data PINCheck = CorrectPIN | IncorrectPIN

data HasCard : ATMState -> Type where
  HasCardInserted : HasCard CardInserted
  HasSession      : HasCard Session

data ATMCmd : (ty : Type) -> ATMState -> (ty -> ATMState) -> Type where
  InsertCard : ATMCmd ()  Ready        (const CardInserted)
  EjectCard  : { auto proof' : HasCard state } ->
               ATMCmd ()  state        (const Ready)
  GetPIN     : ATMCmd PIN CardInserted (const CardInserted)

  CheckPIN : PIN -> ATMCmd PINCheck CardInserted (\check => (case check of
                                                                  CorrectPIN => Session
                                                                  IncorrectPIN => CardInserted))
  GetAmount : ATMCmd Nat state (const state)
  Dispense : (amount : Nat) -> ATMCmd () Session (const Session)
  Message : String -> ATMCmd () state (const state)
  Pure : (res : ty) -> ATMCmd ty (state_fn res) state_fn
  (>>=) : ATMCmd a state1 state2_fn ->
          ((res : a) -> ATMCmd b (state2_fn res) state3_fn) ->
          ATMCmd b state1 state3_fn

-- badATM : ATMCmd () Ready (const Ready)
-- badATM = EjectCard

atm : ATMCmd () Ready (const Ready)
atm = do InsertCard
         pin <- GetPIN
         pinOK <- CheckPIN pin
         case pinOK of
              CorrectPIN => do cash <- GetAmount
                               Dispense cash
                               EjectCard
              IncorrectPIN => EjectCard

atm2 : ATMCmd () Ready (const Ready)
atm2 = do InsertCard
          pin <- GetPIN
          cash <- GetAmount
          pinOK <- CheckPIN pin
          Message "checking card..."
          case pinOK of
               CorrectPIN => do Dispense cash
                                EjectCard
                                Message "please remove card and cash"
               IncorrectPIN => do Message "incorrect PIN"
                                  EjectCard

testPIN : Vect 4 Char
testPIN = ['1', '2', '3', '4']

readVect : (n : Nat) -> IO (Vect n Char)
readVect Z = do _ <- getLine
                pure []
readVect (S k) = do ch <- getChar
                    chs <- readVect k
                    pure (ch :: chs)

runATM : ATMCmd res in_state out_state_fn -> IO res
runATM InsertCard = do putStrLn "please insert card (Enter)"
                       x <- getLine
                       pure ()
runATM EjectCard = putStrLn "card ejected.."
runATM GetPIN = do putStr "enter PIN: "
                   readVect 4
runATM (CheckPIN pin) = if pin == testPIN
                           then pure CorrectPIN
                           else pure IncorrectPIN
runATM GetAmount = do putStr "how much?: "
                      x <- getLine
                      pure $ cast x
runATM (Dispense amount) = putStrLn $ "here is " ++ show amount
runATM (Message msg) = putStrLn msg
runATM (Pure res) = pure res
runATM (x >>= f) = do x' <- runATM x
                      runATM $ f x'

-- exercises --
namespace exercise1
  data Access = LoggedOut | LoggedIn
  data PwdCheck = Correct | InCorrect

  data ShellCmd : (ty : Type) -> Access -> (ty -> Access) -> Type where
    Password : String -> ShellCmd PwdCheck LoggedOut (\pw_check => (case pw_check of
                                                                         Correct => LoggedIn
                                                                         InCorrect => LoggedOut))
    Logout : ShellCmd () LoggedIn (const LoggedOut)
    GetSecret : ShellCmd String LoggedIn (const LoggedIn)

    PutStr : String -> ShellCmd () state (const state)
    Pure : (res : a) -> ShellCmd a (state_fn res) state_fn
    (>>=) : ShellCmd a state1 state2_fn ->
            ((res : a) -> ShellCmd b (state2_fn res) state3_fn) ->
            ShellCmd b state1 state3_fn

  session : ShellCmd () LoggedOut (const LoggedOut)
  session = do Correct <- Password "foobar" | InCorrect => PutStr "wrong pw"
               msg <- GetSecret
               PutStr $ "secret code: " ++ show msg ++ "\n"
               Logout

  -- following must not typecheck
  {-
  bad_session : ShellCmd () LoggedOut (const LoggedOut)
  bad_session = do Password "foo"
                   msg <- GetSecret
                   PutStr $ "secret code is " ++ show msg ++ "\n"
                   Logout
  -}
  -- following must not typecheck
  {-
  noLogout : ShellCmd () LoggedOut (const LoggedOut)
  noLogout = do Correct <- Password "foo" | InCorrect => PutStr "wrong pw"
                msg <- GetSecret
                PutStr $ "secret code: " ++ show msg ++ "\n"
  -}

namespace exercise2
  data CoinResult = Inserted | Rejected

  VendState : Type
  VendState = (Nat, Nat)

  data Input = COIN
             | VEND
             | CHANGE
             | REFILL Nat

  data MachineCmd : (ty : Type) -> VendState -> (ty -> VendState) -> Type where
    InsertCoin : MachineCmd CoinResult (pounds, chocs) (\res => (case res of
                                                                      Inserted => (S pounds, chocs)
                                                                      Rejected => (pounds, chocs)))
    Vend       : MachineCmd () (S pounds, S chocs) (const (pounds, chocs))
    GetCoins   : MachineCmd () (pounds, chocs) (const (Z, chocs))
    Refill     : (bars : Nat) -> MachineCmd () (Z, chocs) (const (Z, bars + chocs))
    Display    : String -> MachineCmd () state (const state)
    GetInput   : MachineCmd (Maybe Input) state (const state)

    Pure : (res : a) -> MachineCmd a (state_fn res) state_fn
    (>>=) : MachineCmd a state1 state2_fn ->
            ((res : a) -> MachineCmd b (state2_fn res) state3_fn) ->
            MachineCmd b state1 state3_fn

  data MachineIO : VendState -> Type where
    Do : MachineCmd a state1 state2_fn ->
         ((res : a) -> Inf (MachineIO (state2_fn res))) ->
         MachineIO state1 -- starting state of a machine

  namespace MachineDo
    (>>=) : MachineCmd a state1 state2_fn ->
            ((res : a) -> Inf (MachineIO (state2_fn res))) ->
            MachineIO state1
    (>>=) = Do

  mutual
    vend : MachineIO (pounds, chocs)
    vend {pounds = Z} = Display "insert coin" >>= (\_ => machineLoop)
    vend {chocs = Z} = Display "out of stock" >>= (\_ => machineLoop)
    vend {pounds = (S k)} {chocs = (S j)} =
      do Vend
         Display "enjoy"
         machineLoop

    refill : (num : Nat) -> MachineIO (pounds, chocs)
    refill {pounds = Z} num = Refill num >>= (\_ => machineLoop)
    refill _ = do Display "can't refill chocolate: coins in machine"
                  machineLoop

    machineLoop : MachineIO (pounds, chocs)
    machineLoop =
      do Just x <- GetInput
                 | Nothing => do Display "invalid input"
                                 machineLoop
         case x of
              COIN => do Inserted <- InsertCoin | Rejected =>do Display "coin rejected"
                                                                machineLoop
                         machineLoop
              VEND => vend
              CHANGE => do GetCoins
                           Display "change returned"
                           machineLoop
              REFILL num => refill num

