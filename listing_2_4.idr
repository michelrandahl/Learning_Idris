module Main

twice : (a -> a) -> a -> a
twice f x = f (f x)

Shape : Type
rotate : Shape -> Shape

double : Num a => a -> a
double x = x * x

quadrople : Num a => a -> a
quadrople = twice double

turn_around : Shape -> Shape
turn_around = twice rotate
