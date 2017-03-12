module Palindrome

||| Checks if a string is a palindrome
palindrome : Nat -> String -> Bool
palindrome len str =
  let str_low = toLower str in
  if length str_low > len then
    str_low == (reverse str_low)
  else
    False

||| calc number of words and chars in a string
counts : String -> (Nat, Nat)
counts str =
  let ws  = length (words str)
      chs = length str
  in (ws, chs)

||| calc top ten largest vals in a list
top_ten : Ord a => List a -> List a
top_ten xs =
  let sorted = sort xs in
  take 10 (reverse sorted)

||| calc number of strings which are longer than n
over_length : Nat -> List String -> Nat
over_length n xs =
  let xs' = filter (\x => length x > n ) xs in
  length xs'
