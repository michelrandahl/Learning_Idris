import Data.Vect

data Vect2 : Nat -> Type -> Type where
  Nil : Vect2 Z a
  (::) : (x : a) -> (xs : Vect2 k a) -> Vect2 (S k) a
%name Vect2 xs, ys, zs

append : Vect n elem -> Vect m elem -> Vect (n+m) elem
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

zip2 : Vect n a -> Vect n b -> Vect n (a,b)
zip2 [] ys = []
zip2 (x :: xs) (y :: ys) = (x, y) :: zip2 xs ys


tryIndex : Integer -> Vect n a -> Maybe a
tryIndex {n} i xs = case integerToFin i n of
                         Nothing => Nothing
                         Just idx => Just (index idx xs)

take2 : (n: Nat) -> Vect (n+m) a -> Vect n a
take2 Z xs = []
take2 (S k) (x :: xs) = x :: (take2 k xs)

sumEntries : Num a => (pos: Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries {n} pos xs ys = case integerToFin pos n of
                                Nothing => Nothing
                                Just idx => Just (index idx xs + index idx ys)
