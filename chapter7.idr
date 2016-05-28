occurrences : Eq ty => (item : ty) -> (values : List ty) -> Nat
occurrences item [] = 0
occurrences item (value :: values) =
  case value == item of
       False => occurrences item values
       True  => 1 + occurrences item values

data Matter = Solid | Liquid | Gas

Eq Matter where
  (==) Solid Solid = True
  (==) Liquid Liquid = True
  (==) Gas Gas = True
  (==) _ _ = False

  (/=) x y = not (x == y)

test : Nat
test = occurrences Gas [Gas, Solid, Liquid]

data Tree elem = Empty
               | Node (Tree elem) elem (Tree elem)

Functor Tree where
  map func Empty = Empty
  map func (Node left e right) =
    Node (map func left)
         (func e)
         (map func right)

Foldable Tree where
  foldr func acc Empty = acc
  foldr func acc (Node left e right) =
    let left_fold  = foldr func acc left
        right_fold = foldr func left_fold right in
        func e right_fold

Eq elem => Eq (Tree elem) where
  (==) Empty Empty = True
  (==) (Node left e right) (Node left' e' right') =
    left == left' && e == e' && right == right'
  (==) _ _ = False


record Album where
  constructor MkAlbum
  artist : String
  title  : String
  year   : Integer

help : Album
help = MkAlbum "The Beatles" "Help" 1965

rubbersoul : Album
rubbersoul = MkAlbum "The Beatles" "rubbersoul" 1965

clouds : Album
clouds = MkAlbum "joni mitchell" "clouds" 1969

hunkydory : Album
hunkydory = MkAlbum "david bowie" "hunky dori" 1971

heroes : Album
heroes = MkAlbum "david bowie" "heroes" 1977

collection : List Album
collection = [help, rubbersoul, hunkydory, clouds, heroes]

Eq Album where
  (==) (MkAlbum artist title year) (MkAlbum artist' title' year') =
    artist == artist' &&
    title == title' &&
    year == year'

Ord Album where
  compare (MkAlbum artist title year) (MkAlbum artist' title' year') =
    case compare artist artist' of
         EQ =>
              case compare year year' of
                   EQ        => compare title title'
                   diff_year => diff_year
         diff_artist => diff_artist

Show Album where
  show (MkAlbum artist title year) =
    title ++ " by " ++ artist ++ " (released " ++ show year ++ ")"

data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

area : Shape -> Double
area (Triangle base height) = 0.5 * base * height
area (Rectangle length height) = length * height
area (Circle radius) = pi * radius * radius

Eq Shape where
  (==) (Triangle x z) (Triangle y w) = x == y && z == w
  (==) (Rectangle x z) (Rectangle y w) = x == y && z == w
  (==) (Circle x) (Circle y) = x == y
  (==) _ _ = False

Ord Shape where
  compare x y = compare (area x) (area y)

data Expr num = Val num
              | Add (Expr num) (Expr num)
              | Sub (Expr num) (Expr num)
              | Mul (Expr num) (Expr num)
              | Div (Expr num) (Expr num)
              | Abs (Expr num)

Show ty => Show (Expr ty) where
  show (Val x) = show x
  show (Add x y) = show x ++ " + " ++ show y
  show (Sub x y) = show x ++ " - " ++ show y
  show (Mul x y) = show x ++ " * " ++ show y
  show (Div x y) = show x ++ " / " ++ show y
  show (Abs x) = "|" ++ show x ++ "|"

eval : (Neg num, Integral num) => Expr num -> num
eval (Val x) = x
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x * eval y
eval (Div x y) = eval x `div` eval y
eval (Abs x) = abs (eval x)

Functor Expr where
  map f (Val x) = Val (f x)
  map f (Add x y) = Add (map f x) (map f y)
  map f (Sub x y) = Sub (map f x) (map f y)
  map f (Mul x y) = Mul (map f x) (map f y)
  map f (Div x y) = Div (map f x) (map f y)
  map f (Abs x) = Abs (map f x)

(Eq ty, Neg ty, Integral ty) => Eq (Expr ty) where
  (==) x y = eval x == eval y

Num ty => Num (Expr ty) where
  (+) = Add
  (*) = Mul
  fromInteger = Val . fromInteger

Neg ty => Neg (Expr ty) where
  negate x = 0 - x
  (-) = Sub
  abs = Abs

(Integral ty, Neg ty) => Cast (Expr ty) ty where
  cast x = eval x

Cast (Maybe elem) (List elem) where
  cast Nothing = []
  cast (Just x) = [x]

totalLen : List String -> Nat
totalLen xs = foldr (\str, len => length str + len) 0 xs

data MyVect : Nat -> Type -> Type where
  Nil  : MyVect Z a
  (::) : (x : a) -> (xs : MyVect k a) -> MyVect (S k) a

Eq a => Eq (MyVect n a) where
  (==) [] [] = True
  (==) (x :: xs) (y :: ys) =
    x == y && xs == ys

Foldable (MyVect n) where
  foldr f acc [] = acc
  foldr f acc (x :: xs) =
    let right_fold = foldr f acc xs in
    f x right_fold


