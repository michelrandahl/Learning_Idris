module Main

data Vect : Nat -> Type -> Type where
     Nil  : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a


data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
  Same : (num : Nat) -> EqNat num num

sameS : (k : Nat) -> (j : Nat) -> (eq : EqNat k j) -> EqNat (S k) (S j)
sameS j j (Same j) = Same (S j)

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat Z Z = Just (Same Z)
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) =
  case checkEqNat k j of
       Nothing => Nothing
       Just eq => Just (sameS _ _ eq)

exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength {m} len input =
  case checkEqNat m len of
       Nothing => Nothing
       Just (Same len) => Just input


-- using prelude functions instead of Same, sameS and EqNat
-- Refl is an instance of the type (=), just like Same is an instance of EqNat
checkEqNat2 : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
checkEqNat2 Z Z = Just Refl
checkEqNat2 Z (S k) = Nothing
checkEqNat2 (S k) Z = Nothing
checkEqNat2 (S k) (S j) =
  case checkEqNat2 k j of
       Nothing => Nothing
       Just x  => Just (cong x) -- cong is similar to sameS, eg. a = b entails (S a) = (S b)

exactLength2 : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength2 {m} len input =
  case checkEqNat2 m len of
       Nothing => Nothing
       Just Refl => Just input

same_cons : {xs : List a} -> {ys : List a} ->
            xs = ys ->
            x :: xs = x :: ys
same_cons Refl = Refl

same_lists : {xs : List a} -> {ys : List a} ->
             x = y ->
             xs = ys ->
             x :: xs = y :: ys
same_lists Refl Refl = Refl

data ThreeEq : a -> b -> c -> Type where
  SameThree : ThreeEq a a a

allSameS : (x, y, z : Nat) ->
           ThreeEq x y z ->
           ThreeEq (S x) (S y) (S z)
allSameS z z z SameThree = SameThree


