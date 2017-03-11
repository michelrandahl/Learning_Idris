module InteractiveBasics

import Data.Vect

allLengths : List String -> List Nat
allLengths [] = []
allLengths (word :: words) = length word :: allLengths words

xor : Bool -> Bool -> Bool
xor False y = y
xor True y = not y


mutual
  isEven : Nat -> Bool
  isEven Z = True
  isEven (S k) = isOdd k

  isOdd : (k : Nat) -> Bool
  isOdd Z = False
  isOdd (S k) = isEven k

fourInts : Vect 4 Int
fourInts = [0, 1, 2, 3]

sixInts : Vect 6 Int
sixInts = [4,5,6,7,8,9]

tenInts : Vect 10 Int
tenInts = fourInts ++ sixInts

allLengths2 : Vect len String -> Vect len Nat
allLengths2 [] = []
allLengths2 (x :: xs) = length x :: allLengths2 xs


insSort : Ord elem => Vect n elem -> Vect n elem
insSort [] = []
insSort (x :: xs) =
  let xsSorted = insSort xs in
      insert x xsSorted
  where
    insert : Ord elem => (x : elem) -> (xsSorted : Vect len elem) -> Vect (S len) elem
    insert x [] = [x]
    insert x (y :: xs) =
      if x < y
      then x :: y :: xs
      else y :: insert x xs


transposeMat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat [] = createEmpties
  where
    createEmpties : Vect n (Vect 0 elem)
    createEmpties {n = Z} = []
    createEmpties {n = (S k)} = [] :: createEmpties
transposeMat (x :: xs) =
  let xsTrans = transposeMat xs in
      zipWith (::) x xsTrans

append : Vect n elem -> Vect m elem -> Vect (n + m) elem
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

my_append : Vect 2 Char -> Vect 2 Char -> Vect 4 Char
my_append = append



