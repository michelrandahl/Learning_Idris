module Section2

-- section 2 of chapter 13, with exercises

import Data.Vect

%default total

data StackCmd : Type -> (before : Nat ) -> (after : Nat) -> Type where
  Push : Integer -> StackCmd () height (S height )
  Pop : StackCmd Integer (S height) height
  Top : StackCmd Integer (S height) (S height)

  GetStr : StackCmd String height height
  PutStr : String -> StackCmd () height height

  Pure : ty -> StackCmd ty height height
  (>>=) : StackCmd a height1 height2 ->
          (a -> StackCmd b height2 height3) ->
          StackCmd b height1 height3

testAdd : StackCmd Integer 0 0
testAdd = do Push 10
             Push 20
             x <- Pop
             y <- Pop
             Pure $ x + y

doAction : (Integer -> Integer -> Integer) ->
           StackCmd () (S (S height)) (S height)
doAction f = do x <- Pop
                y <- Pop
                Push $ f y x

doNegate : StackCmd () (S height) (S height)
doNegate = Pop >>= Push . negate

doDuplicate : StackCmd () (S height) (S (S height))
doDuplicate = Top >>= Push

doDiscard : StackCmd () (S height) height
doDiscard = do _ <- Pop; Pure ()

runStack : (stack : Vect height_before Integer) ->
           StackCmd ty height_before height_after ->
           IO (ty, Vect height_after Integer)
runStack stack (Push x) = pure ((), x :: stack)
runStack (x :: xs) Pop = pure (x, xs)
runStack (x :: xs) Top = pure (x, x :: xs)
runStack stack (Pure x) = pure (x, stack)
runStack stack (cmd >>= f) =
  do (x, new_stack) <- runStack stack cmd
     runStack new_stack $ f x
runStack stack GetStr = do x <- getLine; pure (x, stack)
runStack stack (PutStr x) = do putStr x; pure ((), stack)

data StackIO : Nat -> Type where
  Do : StackCmd a height1 height2 ->
       (a -> Inf (StackIO height2)) ->
       StackIO height1

namespace StackDo
  (>>=) : StackCmd a height1 height2 ->
          (a -> Inf (StackIO height2)) ->
          StackIO height1
  (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)
partial
forever : Fuel
forever = More forever

run : Fuel -> Vect height Integer -> StackIO height -> IO ()
run Dry stack _ = pure ()
run (More fuel) stack (Do cmd f) =
  do (x, new_stack) <- runStack stack cmd
     run fuel new_stack $ f x

data StackInput = Number Integer
                | Add
                | Subtract
                | Multiply
                | Negate
                | Duplicate
                | Discard

stringToInput : String -> Maybe StackInput
stringToInput "" = Nothing
stringToInput "add" = Just Add
stringToInput "subtract" = Just Subtract
stringToInput "multiply" = Just Multiply
stringToInput "negate" = Just Negate
stringToInput "duplicate" = Just Duplicate
stringToInput "discard" = Just Discard
stringToInput x =
  if all isDigit (unpack x)
     then Just $ Number $ cast x
     else Nothing

mutual
  tryAction : (Integer -> Integer -> Integer) -> StackIO height
  tryAction {height = (S (S k))} f =
    do doAction f
       showResult
  tryAction _ = do PutStr "fewer than two items on the stack\n"
                   stackCalc

  reportZeroItems : StackCmd () height height
  reportZeroItems = PutStr "zero items on stack\n"

  tryNegate : StackIO height
  tryNegate {height = (S k)} =
    do doNegate
       showResult
  tryNegate = do reportZeroItems
                 stackCalc

  showResult : StackIO height
  showResult {height = (S k)} =
    do result <- Top
       PutStr $ show result ++ "\n"
       stackCalc
  showResult = do reportZeroItems
                  stackCalc

  tryDuplicate : StackIO height
  tryDuplicate {height = (S k)} =
    do x <- Top
       doDuplicate
       PutStr $ "duplicated " ++ show x ++ "\n"
       stackCalc
  tryDuplicate = do reportZeroItems
                    stackCalc

  tryDiscard : StackIO height
  tryDiscard {height = (S k)} =
    do x <- Top
       doDiscard
       PutStr $ "discarded " ++ show x ++ "\n"
       stackCalc
  tryDiscard = do reportZeroItems
                  stackCalc

  performAction : StackInput -> StackIO height
  performAction (Number x) = do Push x; stackCalc
  performAction Add = tryAction (+)
  performAction Subtract = tryAction (-)
  performAction Multiply = tryAction (*)
  performAction Negate = tryNegate
  performAction Duplicate = tryDuplicate
  performAction Discard = tryDiscard

  stackCalc : StackIO height
  stackCalc =
    do PutStr "> "
       input <- GetStr
       case stringToInput input of
            Nothing => do PutStr "invalid input\n"; stackCalc
            Just parsed => performAction parsed

partial
main : IO ()
main = run forever [] stackCalc


