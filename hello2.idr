-- various code from the first three chapters
module Main
import Data.Vect

main : IO ()
main = putStrLn "hello idris"

word_lengths : List String -> List Nat
word_lengths strs = map length strs

invert : Bool -> Bool
invert False = True
invert True = False

describe_list : List Int -> String
describe_list [] = "Empty"
describe_list (x :: xs) = "Non empty, tail = " ++ show xs

mutual
    isEven : Nat -> Bool
    isEven Z = True
    isEven (S k) = isOdd k

    isOdd : Nat -> Bool
    isOdd Z = False
    isOdd (S k) = isEven k

fourInts : Vect 4 Int
fourInts = [0,1,2,3]

sixInts : Vect 6 Int
sixInts = [4,5,6,7,8,9]

tenInts : Vect 10 Int
tenInts = fourInts ++ sixInts

insert : Ord elem => (x : elem) -> (xs_sorted : Vect k elem) -> Vect (S k) elem
insert x [] = [x]
insert x (y :: xs) =
    case x < y of
        False => y :: insert x xs
        True => x :: y :: xs

ins_sort : Ord elem => Vect n elem -> Vect n elem
ins_sort [] = []
ins_sort (x :: xs) =
    let xs_sorted = ins_sort xs in
    insert x xs_sorted

my_length : List a -> Nat
my_length [] = 0
my_length (x :: xs) = 1 + my_length xs

my_reverse : List a -> List a
my_reverse [] = []
my_reverse (x :: xs) =
    (my_reverse xs) ++ [x]

my_map : (a -> b) -> List a -> List b
my_map f [] = []
my_map f (x :: xs) =
    f x :: my_map f xs

my_map2 : (a -> b) -> Vect n a -> Vect n b
my_map2 f [] = []
my_map2 f (x :: xs) = f x :: my_map2 f xs

||| Very silly append function
||| can be used like this:
|||   > silly_append Char 2 2 ['a','b'] ['c','d']
||| but also like this:
|||   > silly_append _ _ _ ['a','b'] ['c','d']
silly_append : (elem : Type) -> (n : Nat) -> (m : Nat) ->
         Vect n elem -> Vect m elem -> Vect (n + m) elem
silly_append elem Z m [] ys = ys
silly_append elem (S k) m (x :: xs) ys =
  x :: silly_append elem k m xs ys

silly_append2 : {elem: _} -> {n : _} -> {m : _} ->
                Vect n elem -> Vect m elem -> Vect (n + m) elem
silly_append2 [] ys = ys
silly_append2 (x :: xs) ys =
  x :: silly_append2 xs ys
