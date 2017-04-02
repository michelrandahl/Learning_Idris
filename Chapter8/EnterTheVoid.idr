module EnterTheVoid

twoPlusTwoNotFive : 2 + 2 = 5 -> Void
twoPlusTwoNotFive Refl impossible

valueNotSucc : (x : Nat) -> x = S x -> Void
valueNotSucc _ Refl impossible





noRec : (contra : (k = j) -> Void) -> (S k = S j) -> Void
noRec contra Refl = contra Refl

checkEqNat : (n1 : Nat) -> (n2 : Nat) -> Dec (n1 = n2)
checkEqNat Z Z = Yes Refl
checkEqNat Z (S k) = No zeroNotSucc
  where
    zeroNotSucc : (0 = S k) -> Void
    zeroNotSucc Refl impossible
checkEqNat (S k) Z = No succNotZero
  where
    succNotZero : (S k = 0) -> Void
    succNotZero Refl impossible
checkEqNat (S k) (S j) =
  case checkEqNat k j of
       Yes prf => Yes (cong prf)
       No contra => No (noRec contra)
