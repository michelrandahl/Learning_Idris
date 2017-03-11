module Exercises

-- Exercises 1
ex1_1 : (String, String, String)
ex1_1 = ("A", "B", "C")

ex1_2 : List String
ex1_2 = ["A", "B", "C"]

ex1_3 : ((String, String), String)
ex1_3 = (("A", "B"), "C")

ex1_3a : (String, String, String)
ex1_3a = ("A", ("B", "C")) -- <- note the conversion to (x,y,z)


-- Exercises 2-5
palindrome : Nat -> String -> Bool
palindrome n x =
  if length x > n
  then True
  else let x' = toLower x in
       (reverse x') == x'

-- Exercises 6
counts : String -> (Nat, Nat)
counts x = (length (words x), length x)

-- Exercises 7
top_ten : Ord a => List a -> List a
top_ten xs = take 10 (reverse (sort xs))

-- Exercises 8
over_length : Nat -> List String -> Nat
over_length k xs = length (filter (\x => length x > k) xs)

main : IO ()
main = ?main_rhs
