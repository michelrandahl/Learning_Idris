module Exercises

data Elem : a -> List a -> Type where
  Here  : Elem x (x :: xs)
  There : (later : Elem x xs) -> Elem x (y :: xs)

data Last : List a -> a -> Type where
  LastOne  : Last [x] x
  LastCons : (prf : Last xs value) -> Last (x :: xs) value

last123 : Last [1,2,3] 3
last123 = LastCons (LastCons LastOne)

notLastElem : (contra : (x = value) -> Void) -> Last [x] value -> Void
notLastElem contra LastOne = contra Refl
notLastElem _ (LastCons LastOne) impossible
notLastElem _ (LastCons (LastCons _)) impossible

lastNotNil : Last [] value -> Void
lastNotNil LastOne impossible
lastNotNil (LastCons _) impossible

notInCons : (contra : Last (x :: xs) value -> Void) -> Last (y :: x :: xs) value -> Void
notInCons contra (LastCons prf) = contra prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No lastNotNil
isLast (x :: []) value =
  case decEq x value of
       Yes Refl => Yes LastOne
       No contra => No (notLastElem contra)
isLast (y :: x :: xs) value =
  case isLast (x :: xs) value of
       Yes prf => Yes (LastCons prf)
       No contra => No (notInCons contra)

