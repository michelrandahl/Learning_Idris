module Main

import Data.Vect
import Data.List.Views
import Data.Vect.Views
import Data.Nat.Views

data TakeN : List a -> Type where
  Fewer : TakeN xs
  Exact : (xs : List a) -> TakeN (xs ++ rest)

total
takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z xs = Exact []
takeN (S k) [] = Fewer
takeN (S k) (x :: xs) =
  case takeN k xs of
       Fewer => Fewer
       Exact xs => Exact (x :: xs)

groupN : (n : Nat) -> (xs : List a) -> List (List a)
groupN n xs with (takeN n xs)
  groupN n xs           | Fewer = [xs]
  groupN n (ys ++ rest) | Exact ys =
    ys :: groupN n rest

halves : (xs : List a) -> (List a, List a)
halves xs with (takeN (length xs `div` 2) xs)
  halves xs           | Fewer = (xs,[])
  halves (ys ++ rest) | Exact ys = (ys,rest)

total
equalSuffix : Eq a => List a -> List a -> List a
equalSuffix xs' ys' with (snocList xs')
  equalSuffix [] ys                | Empty = []
  equalSuffix (xs'' ++ [x'']) ys'' | (Snoc rec) with (snocList ys'')
    equalSuffix (xs ++ [x]) []          | Snoc rec    | Empty = []
    equalSuffix (xs ++ [x]) (ys ++ [y]) | Snoc xs_rec | Snoc ys_rec =
      if x == y
      then (equalSuffix xs ys | xs_rec | ys_rec) ++ [x]
      else []

total
mergeSort : Ord a => Vect n a -> Vect n a
mergeSort xs' with (splitRec xs')
  mergeSort []         | SplitRecNil = []
  mergeSort [x]        | SplitRecOne = [x]
  mergeSort (xs ++ ys) | SplitRecPair lrec rrec =
    merge (mergeSort xs | lrec)
          (mergeSort ys | rrec)

total
toBinary : (n : Nat) -> String
toBinary Z = "0"
toBinary n' with (halfRec n')
  toBinary Z           | HalfRecZ = ""
  toBinary (x + x)     | HalfRecEven rec = toBinary x | rec ++ "0"
  toBinary (S (x + x)) | HalfRecOdd rec = toBinary x | rec ++ "1"

total
palindrome : Eq a => List a -> Bool
palindrome xs with (vList xs)
  palindrome []               | VNil = True
  palindrome [x]              | VOne = True
  palindrome (x :: xs ++ [y]) | VCons rec =
    if x == y
    then palindrome xs | rec
    else False






