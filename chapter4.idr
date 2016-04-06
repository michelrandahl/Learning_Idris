import Data.Vect

data Direction = North
               | East
               | South
               | West

turn_clockwise : Direction -> Direction
turn_clockwise North = East
turn_clockwise East = South
turn_clockwise South = West
turn_clockwise West = North


||| Represents shapes
data Shape =
             ||| A triangle with its base, length and height
             Triangle Double Double
           | ||| A rectangle with its length and height
             Rectangle Double Double
           | ||| A circle with its radius
             Circle Double

area : Shape -> Double
area (Triangle base height) = 0.5 * base * height
area (Rectangle length height) = length * height
area (Circle radius) = pi * radius * radius


data Picture = Primitive Shape
             | Combine Picture Picture
             | Rotate Double Picture
             | Translate Double Double Picture
%name Shape shape, shape1, shape2
%name Picture pic, pic1, pic2

rectangle : Picture
rectangle = Primitive (Rectangle 20 10)

circle : Picture
circle = Primitive (Circle 5)

triangle : Picture
triangle = Primitive (Triangle 10 10)

test_picture : Picture
test_picture =
  Combine (Translate 5 5 rectangle)
  (Combine (Translate 35 5 circle)
  (Translate 15 25 triangle))

picture_area : Picture -> Double
picture_area (Primitive shape) = area shape
picture_area (Combine pic pic1) = picture_area pic + picture_area pic1
picture_area (Rotate x pic) = picture_area pic
picture_area (Translate x y pic) = picture_area pic

safe_divide : Double -> Double -> Maybe Double
safe_divide x y = if y == 0 then Nothing
                            else Just (x/y)

data Tree elem = Empty
               | Node (Tree elem) elem (Tree elem)
%name Tree tree, tree1, tree2

insert : Ord elem => elem -> Tree elem -> Tree elem
insert x Empty = Node Empty x Empty
insert x orig@(Node left val right) = case compare x val of
                                      LT => Node (insert x left) val right
                                      EQ => orig -- using the orig
                                      GT => Node left val (insert x right)

listToTree : Ord a => List a -> Tree a
listToTree [] = Empty
listToTree (x :: xs) = insert x (listToTree xs)

treeToList : Tree a -> List a
treeToList Empty = []
treeToList (Node tree x tree1) = (treeToList tree) ++ [x] ++ (treeToList tree1)

-- alternative binary search tree data type
-- specifying the type to require the Ord class for elements
data BSTree : Type -> Type where
     Empty2 : Ord elem => BSTree elem
     Node2  : Ord elem => (left: BSTree elem) -> (val: elem) -> (right: BSTree elem) -> BSTree elem

insert2 : elem -> BSTree elem -> BSTree elem
insert2 x Empty2 = Node2 Empty2 x Empty2
insert2 x orig@(Node2 left val right) = case compare x val of
                                        LT => Node2 (insert2 x left) val right
                                        EQ => orig -- using the orig@ pattern
                                        GT => Node2 left val (insert2 x right)

data Expr = Val Int
          | Addition Expr Expr
          | Subtraction Expr Expr
          | Multiplication Expr Expr

evaluate : Expr -> Int
evaluate (Val x) = x
evaluate (Addition x y) = evaluate x + evaluate y
evaluate (Subtraction x y) = evaluate x - evaluate y
evaluate (Multiplication x y) = evaluate x * evaluate y

maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing Nothing = Nothing
maxMaybe Nothing (Just x) = Just x
maxMaybe (Just x) Nothing = Just x
maxMaybe (Just x) (Just y) = Just (max x y)

biggestTriangle : Picture -> Maybe Double
biggestTriangle (Primitive triangle@(Triangle x y)) = Just(area triangle)
biggestTriangle (Primitive _) = Nothing
biggestTriangle (Combine pic pic1) =
  let
    res1 = biggestTriangle pic
    res2 = biggestTriangle pic1
  in
    maxMaybe res1 res2
biggestTriangle (Rotate x pic) = biggestTriangle pic
biggestTriangle (Translate x y pic) = biggestTriangle pic

data PowerSource = Petrol | Pedal | Electric

data Vehicle     : PowerSource -> Type where
     Bicycle     : Vehicle Pedal
     Unicycle    : Vehicle Pedal
     Tram        : Vehicle Electric
     ElectricCar : Vehicle Electric
     Motercycle  : (fuel : Nat) -> Vehicle Petrol
     Car         : (fuel : Nat) -> Vehicle Petrol
     Bus         : (fuel : Nat) -> Vehicle Petrol

wheels : Vehicle power -> Nat
wheels Bicycle = 2
wheels (Car fuel) = 4
wheels (Bus fuel) = 4
wheels (Motercycle fuel) = 2
wheels Unicycle = 1

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Car fuel) = Car 100
refuel (Bus fuel) = Bus 200
refuel (Motercycle fuel) = Motercycle 30
refuel Bicycle impossible
refuel Unicycle impossible

tryIndex : Integer -> Vect n a -> Maybe a
tryIndex {n} i xs = case integerToFin i n of
                         Nothing => Nothing
                         (Just idx) => Just (index idx xs)

take2 : (n: Nat) -> Vect (n+m) a -> Vect n a
take2 Z _ = []
take2 (S n) (x :: xs) = x :: (take2 n xs)

sumEntries : Num a => (pos: Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries _ [] [] = Nothing
sumEntries {n} pos xs ys =
  case integerToFin pos n of
       Nothing => Nothing
       (Just idx) => Just (index idx xs + index idx ys)


