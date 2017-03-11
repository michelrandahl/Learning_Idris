module UserDefinedDataTypes

import Data.Vect

my_empty_list : List Int
my_empty_list = the (List Int) Nil

-- an enumerated type
data Direction = North
               | East
               | South
               | West

turnClockwise : Direction -> Direction
turnClockwise North = East
turnClockwise East = South
turnClockwise South = West
turnClockwise West = North

-- a union type is an extension of enumerated types.
-- like in F# we can label the data in the union type by writing out the constructors in an explicit style
-- this is convenient when case splitting because idris will use the labels as variable names
data Shape : Type where
  Triangle  : (base : Double) -> (height : Double) -> Shape
  Rectangle : (length : Double) -> (height : Double) -> Shape
  Circle    : (radius : Double) -> Shape

area : Shape -> Double
area (Triangle base height) = 0.5 * base * height
area (Rectangle length height) = length * height
area (Circle radius) = pi * radius * radius

data Picture : Type where
  Primitive : (shape : Shape) -> Picture
  Combine   : (pic1 : Picture) -> (pic2 : Picture) -> Picture
  Rotate    : (angle : Double) -> (pic : Picture) -> Picture
  Translate : (x : Double) -> (y : Double) -> (pic : Picture) -> Picture

rectangle : Picture
rectangle = Primitive (Rectangle 20 10)

circle : Picture
circle = Primitive (Circle 5)

triangle : Picture
triangle = Primitive (Triangle 10 10)

testPicture : Picture
testPicture = Combine (Translate 5 5 rectangle)
                      (Combine (Translate 35 5 circle)
                               (Translate 15 25 triangle))

pictureArea : Picture -> Double
pictureArea (Primitive shape) = area shape
pictureArea (Combine pic1 pic2) = pictureArea pic1 + pictureArea pic2
pictureArea (Rotate angle pic) = pictureArea pic
pictureArea (Translate x y pic) = pictureArea pic

-- data Tree elem = Empty
--                | Node (Tree elem) elem (Tree elem)
-- %name Tree tree, tree1
-- BSTree is a dependent type, because it goes Type -> Type
data BSTree : Type -> Type where
  Empty : Ord elem => BSTree elem
  Node  : Ord elem => (left : BSTree elem) -> (val : elem) -> (right : BSTree elem) -> BSTree elem

insert : elem -> BSTree elem -> BSTree elem
insert x Empty = Node Empty x Empty
insert x orig@(Node left val right) = case compare x val of
                                      LT => Node (insert x left) val right
                                      EQ => orig
                                      GT => Node left val (insert x right)

-- exercises
listToTree : Ord a => List a -> BSTree a
listToTree xs = foldl (\tree,elem => insert elem tree) Empty xs

treeToList : BSTree a -> List a
treeToList Empty = []
treeToList (Node left val right) = treeToList left ++ [val] ++ treeToList right

data PowerSource = Petrol
                 | Pedal
                 | Electric

data Vehicle : PowerSource -> Type where
  Bicycle    : Vehicle Pedal
  Unicycle   : Vehicle Pedal
  MotorCycle : (fuel : Nat) -> Vehicle Petrol
  Car        : (fuel : Nat) -> Vehicle Petrol
  Bus        : (fuel : Nat) -> Vehicle Petrol
  Tram       : Vehicle Electric

wheels : Vehicle power -> Nat
wheels Bicycle = 2
wheels (Car fuel) = 4
wheels (Bus fuel) = 4
wheels (MotorCycle fuel) = 2
wheels Unicycle = 1

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Car fuel) = Car 100
refuel (Bus fuel) = Bus 200
refuel (MotorCycle fuel) = MotorCycle 50

tryIndex : Integer -> Vect n a -> Maybe a
tryIndex {n} i xs = case integerToFin i n of
                         Nothing => Nothing
                         (Just i) => Just (index i xs)

vectTake : (k : Nat) -> Vect (k + n) a -> Vect k a
vectTake Z _ = []
vectTake (S k) (x :: xs) = x :: vectTake k xs

sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries {n} pos xs ys =
  case integerToFin pos n of
    Nothing => Nothing
    (Just i) => Just ((index i xs) + (index i ys))



