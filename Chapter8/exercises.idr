module Exercises

import Data.Vect

myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = rewrite plusZeroRightNeutral m in Refl
myPlusCommutes (S k) m =
  rewrite sym (plusSuccRightSucc m k) in
          let result = myPlusCommutes k m in
              cong result


myReverse : Vect n a -> Vect n a
myReverse xs = reverse' [] xs
  where
    reverseProof_nil : Vect n a -> Vect (plus n 0) a
    reverseProof_nil {n} xs = rewrite plusZeroRightNeutral n in xs

    reverseProof_xs : Vect (S (n + len)) a -> Vect (n + (S len)) a
    reverseProof_xs {n} {len} xs = rewrite sym (plusSuccRightSucc n len) in xs

    reverse' : Vect n a -> Vect m a -> Vect (n + m) a
    reverse' acc [] = reverseProof_nil acc
    reverse' acc (x :: xs) =
      reverseProof_xs (reverse' (x :: acc) xs)

headUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} ->
                         (contra : (x = y) -> Void) ->
                         ((x :: xs) = (y :: ys)) ->
                         Void
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} ->
                         (contra : (xs = ys) -> Void) ->
                         ((x :: xs) = (y :: ys)) ->
                         Void
tailUnequal contra Refl = contra Refl



