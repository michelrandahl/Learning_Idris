module Main

import Data.Vect

data Matter = Solid | Liquid | Gas

Eq Matter where
  (==) Solid Solid = True
  (==) Liquid Liquid = True
  (==) Gas Gas = True
  (==) _ _ = False
  (/=) x y = not (x == y)

occurences : Eq ty => (item : ty) -> (values : List ty) -> Nat
occurences item [] = 0
occurences item (x :: xs) =
  case x == item of
       False => occurences item xs
       True => 1 + occurences item xs

data Tree elem = Empty
               | Node (Tree elem) elem (Tree elem)

Foldable Tree where
  foldr f acc Empty = acc
  foldr f acc (Node left e right) =
    let left_fold = foldr f acc left
        right_fold = foldr f left_fold right in
        f e right_fold

Eq elem => Eq (Tree elem) where
  (==) Empty Empty = True
  (==) (Node left e right) (Node left' e' right') =
    left == left' && e == e' && right == right'
  (==) _ _ = False

Functor Tree where
  map f Empty = Empty
  map f (Node left e right) =
    Node (map f left) (f e) (map f right)

record Album where
  constructor MkAlbum
  artist : String
  title : String
  year : Integer

Eq Album where
  (==) (MkAlbum artist title year) (MkAlbum artist' title' year') =
    artist == artist' && title == title' && year == year'

Ord Album where
  compare (MkAlbum artist title year) (MkAlbum artist' title' year') =
    case compare artist artist' of
         EQ => case compare year year' of
                    EQ        => compare title title'
                    diff_year => diff_year
         diff_artist => diff_artist

Show Album where
  show (MkAlbum artist title year) =
    title ++ " by " ++ artist ++ " (released " ++ show year ++ ")"

help : Album
help = MkAlbum "beatles" "help" 1965

rubbersoul : Album
rubbersoul = MkAlbum "beatles" "rubber soul" 1969

clouds : Album
clouds = MkAlbum "joni mitchell" "clouds" 1971

hunkyory : Album
hunkyory = MkAlbum "david bowie" "hunky dory" 1971

heroes : Album
heroes = MkAlbum "david bowie" "heroes" 1977

collection : List Album
collection = [help, rubbersoul, clouds, hunkyory, heroes]

data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

Eq Shape where
  (==) (Triangle x z) (Triangle x' z') =
    x == x && z == z'
  (==) (Rectangle x z) (Rectangle x' z') =
    x == x' && z == z'
  (==) (Circle x) (Circle x') = x == x'
  (==) _ _ = False

area : Shape -> Double
area (Triangle x y) = (x * y) / 2.0
area (Rectangle x y) = x * y
area (Circle x) = pi * x * x

Ord Shape where
  compare x y = compare (area x) (area y)

testShapes : List Shape
testShapes = [Circle 3, Triangle 3 9, Rectangle 2 6, Circle 4, Rectangle 2 7]

data Expr num = Val num
              | Add (Expr num) (Expr num)
              | Sub (Expr num) (Expr num)
              | Mul (Expr num) (Expr num)
              | Div (Expr num) (Expr num)
              | Abs (Expr num)

Functor Expr where
  map f (Val x) = Val (f x)
  map f (Add x y) = Add (map f x) (map f y)
  map f (Sub x y) = Sub (map f x) (map f y)
  map f (Mul x y) = Mul (map f x) (map f y)
  map f (Div x y) = Div (map f x) (map f y)
  map f (Abs x) = Abs (map f x)

Show num => Show (Expr num) where
   show (Val x) = show x
   show (Add x y) = show x ++ " + (" ++ show y ++ ")"
   show (Sub x y) = show x ++ " - (" ++ show y ++ ")"
   show (Mul x y) = show x ++ " * " ++ show y
   show (Div x y) = show x ++ " / " ++ show y
   show (Abs x) = "|" ++ show x ++ "|"

Num ty => Num (Expr ty) where
  (+) = Add
  (*) = Mul
  fromInteger = Val . fromInteger

Neg ty => Neg (Expr ty) where
  negate x = 0 - x
  (-) = Sub
  abs = Abs

eval : (Neg num, Integral num) => Expr num -> num
eval (Val x)   = x
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x * eval y
eval (Div x y) = eval x `div` eval y
eval (Abs x)   = abs (eval x)

(Eq num, Neg num, Integral num) => Eq (Expr num) where
  (==) x y = eval x == eval y

(Integral num, Neg num) => Cast (Expr num) num where
  cast x = eval x

Cast (Maybe elem) (List elem) where
  cast Nothing = []
  cast (Just x) = [x]

totalLen : List String -> Nat
totalLen xs = foldl (\len, str => length str + len) 0 xs


data MyVect : (n : Nat) -> (t : Type) -> Type where
  Nil  : MyVect Z t
  (::) : (x : t) -> (xs : MyVect n t) -> MyVect (S n) t

Eq t => Eq (MyVect n t) where
  (==) [] [] = True
  (==) (x :: xs) (y :: ys) =
    x == y && xs == ys

Foldable (MyVect n) where
  foldr f acc [] = acc
  foldr f acc (x :: xs) =
    let acc' = foldr f acc xs in
        f x acc'

-- xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
-- x Fooling around with Monads x
-- xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx

x : Maybe Nat
x = Just 42

y : Maybe String
y = Just "hello idris"

z : Maybe Nat
z = Just 4

addStuffBad : Maybe Nat
addStuffBad =
  case x of
       Nothing => Nothing
       (Just x') =>
          case y of
               Nothing => Nothing
               (Just y') =>
                  case z of
                       Nothing => Nothing
                       (Just z') => Just (x' + length y' + z')

addStuffBetter : Maybe Nat
addStuffBetter =
  x >>= (\x' =>
  y >>= (\y' =>
  z >>= (\z' =>
  Just (x' + length y' + z'))))

addStuffNeat : Maybe Nat
addStuffNeat =
  do x' <- x
     y' <- y
     z' <- z
     pure (x' + length y' + z')

-- Attempting to implement my own Maybe monad using the Option type naming from F#
data Option x = None
              | Some x

Functor Option where
  map f None = None
  map f (Some x) = Some (f x)

Applicative Option where
  pure x = Some x
  (<*>) (Some f) (Some x) = Some (f x)
  (<*>) _ _ = None

Monad Option where
  (>>=) None _ = None
  (>>=) (Some x) f = f x

main : IO ()
main =
  do x <- getLine
     let x' = the Integer (cast x)
     let xs = the (Vect _ _) (cast [1 .. x'])
     let res = foldl (+) 0 xs
     printLn (show res)

