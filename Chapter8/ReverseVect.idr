module Main

import Data.Vect

-- following fails with mismatch
-- Actual: Vect (len + 1) ...
-- and
-- Expected: Vect (S len) ...
-- myReverse : Vect n elem -> Vect n elem
-- myReverse [] = []
-- myReverse (x :: xs) = myReverse xs ++ [x]

myReverse1 : Vect n elem -> Vect n elem
myReverse1 {n = Z} [] = []
myReverse1 {n = S len} (x :: xs) =
  let rev_xs = myReverse1 xs
      result = rev_xs ++ [x] in
      -- plus 1 len is the same as len + 1
      rewrite plusCommutative 1 len in
              result

test1 : Vect 4 Int
test1 = [1,2,3,4]

test2 : Vect (2 + 2) Int
test2 = test1


myReverse2 : Vect n elem -> Vect n elem
myReverse2 [] = []
myReverse2 (x :: xs) = reverseProof (myReverse2 xs ++ [x])
  where
    reverseProof : Vect (len + 1) elem -> Vect (S len) elem
    reverseProof {len} result =
      rewrite plusCommutative 1 len in result


-- defining append with (m + n) instead of (n + m)

append_nil : Vect m elem -> Vect (plus m 0) elem
append_nil {m} xs = rewrite plusZeroRightNeutral m in xs

append_xs : Vect (S (m + k)) elem -> Vect (plus m (S k)) elem
append_xs {m} {k} xs =
  rewrite sym (plusSuccRightSucc m k) in
      xs

append : Vect n elem -> Vect m elem -> Vect (m + n) elem
append [] ys = append_nil ys
append (x :: xs) ys =
  let result = (x :: append xs ys) in
      append_xs result





