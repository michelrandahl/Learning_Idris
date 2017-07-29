module Section1

-- section 1 of chapter 13, with exercises

%default total

namespace section_1_1
  data DoorState = DoorClosed
                 | DoorOpen

  data DoorCmd : Type -> (before : DoorState) -> (after : DoorState) -> Type where
    Open  : DoorCmd () DoorClosed DoorOpen
    Close : DoorCmd () DoorOpen   DoorClosed
    --RingBell : DoorCmd () DoorClosed DoorClosed -- original
    RingBell : DoorCmd () state state -- exercise 1: doorbell now works in any state

    Pure : ty -> DoorCmd ty state state
    (>>=) : DoorCmd a state1 state2 ->
            (a -> DoorCmd b state2 state3) ->
            DoorCmd b state1 state3

  doorProg : DoorCmd () DoorClosed DoorClosed
  doorProg = do RingBell
                Open
                Close

  -- exercise 1
  doorProg2 : DoorCmd () DoorClosed DoorClosed
  doorProg2 = do RingBell
                 Open
                 RingBell
                 Close

namespace section_1_3
  VendState : Type
  VendState = (Nat, Nat)

  data Input = COIN
             | VEND
             | CHANGE
             | REFILL Nat

  data MachineCmd : Type -> (before : VendState) -> (after : VendState) -> Type where
    InsertCoin : MachineCmd () (pounds, chocs) (S pounds, chocs)
    Vend       : MachineCmd () (S pounds, S chocs) (pounds, chocs)
    GetCoins   : MachineCmd () (pounds, chocs) (Z, chocs)
    Refill     : (bars : Nat) -> MachineCmd () (Z, chocs) (Z, bars + chocs)
    Display    : String -> MachineCmd () state state
    GetInput   : MachineCmd (Maybe Input) state state

    Pure : ty -> MachineCmd ty state state
    (>>=) : MachineCmd a state1 state2 ->
            (a -> MachineCmd b state2 state3) ->
            MachineCmd b state1 state3

  data MachineIO : VendState -> Type where
    Do : MachineCmd a state1 state2 ->
         (a -> Inf (MachineIO state2)) ->
         MachineIO state1 -- starting state of a machine

  namespace MachineDo
    (>>=) : MachineCmd a state1 state2 ->
            (a -> Inf (MachineIO state2)) ->
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
              COIN => InsertCoin >>= (\_ => machineLoop)
              VEND => vend
              CHANGE => do GetCoins
                           Display "change returned"
                           machineLoop
              REFILL num => refill num


-- EXERCISES --

-- exercise 2:
data GuessCmd : Type -> Nat -> Nat -> Type where
  Try : Integer -> GuessCmd Ordering (S guesses) guesses

  Pure : ty -> GuessCmd ty state state
  (>>=) : GuessCmd a state1 state2 ->
          (a -> GuessCmd b state2 state3) ->
          GuessCmd b state1 state3

threeGuesses : GuessCmd () 3 0
threeGuesses = do Try 10
                  Try 20
                  Try 15
                  Pure ()

-- following must not type check
{-
noGuesses : GuessCmd () 0 0
noGuesses = do Try 10
               Pure ()
-}

-- exercise 3:
namespace exercise_3
  data Matter = Solid | Liquid | Gas

  data MatterCmd : Type -> Matter -> Matter -> Type where
    Melt : MatterCmd () Solid Liquid
    Boil : MatterCmd () Liquid Gas
    Condense : MatterCmd () Gas Liquid
    Freeze : MatterCmd () Liquid Solid

    Pure : ty -> MatterCmd ty state state
    (>>=) : MatterCmd a state1 state2 ->
            (a -> MatterCmd b state2 state3) ->
            MatterCmd b state1 state3

  iceSteam : MatterCmd () Solid Gas
  iceSteam = do Melt
                Boil

  steamIce : MatterCmd () Gas Solid
  steamIce = do Condense
                Freeze

  -- must not type check
  {-
  overMelt : MatterCmd () Solid Gas
  overMelt = do Melt
                Melt
  -}
