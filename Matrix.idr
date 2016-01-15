module Matrix
import Data.Vect

infixl 5 |> -- syntactic bacon
(|>) : a -> (a -> b) -> b
a |> f = f a

add : Num a =>
      Vect n (Vect m a) -> Vect n (Vect m a) ->
      Vect n (Vect m a)
add [] [] = []
add (x :: xs) (y :: ys) =
    let zs = zipWith (\x,y => x+y) x y in
    zs :: add xs ys

create_empties : Vect n (Vect 0 elem)
create_empties = replicate _ []

transposeMat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat [] = create_empties
transposeMat (x :: xs) =
    let xs_trans = transposeMat xs in
    zipWith (\x,y => (x :: y)) x xs_trans

multMatrix : Num a =>
             Vect m (Vect n a) -> Vect n (Vect p a) ->
             Vect m (Vect p a)
multMatrix {m} {n} {p} xs ys =
    let
      ys' = the (Vect m (Vect p (Vect n _)))
            (transposeMat ys
             |> replicate m)
      xs' = the (Vect m (Vect p (Vect n _)))
            (xs |> map (replicate p))
    in
    zipWith multiply_cols xs' ys'
    |> map (map sum)
    where
      multiply_cols : Num a =>
                      Vect m' (Vect n' a) -> Vect m' (Vect n' a) ->
                      Vect m' (Vect n' a)
      multiply_cols xs ys = zipWith (zipWith (*)) xs ys

