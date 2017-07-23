module Main

data SnocList : List a -> Type where
  Empty : SnocList []
  Snoc  : (rec : SnocList xs) -> SnocList (xs ++ [x])

-- playing around with instantiating the above type
test1 : SnocList [] {a = Int}
test1 = Empty

test2 : SnocList [1]
test2 = Snoc Empty

test3 : SnocList [1,2]
test3 = Snoc (Snoc Empty)

test4 : SnocList [42]
test4 = Snoc {rec = Empty} {x = 42}

test5 : SnocList [1,2,3]
test5 = Snoc (Snoc (Snoc Empty {x = 1}) {x = 2}) {x = 3}

total
snocListHelper : (acc : SnocList input) -> (rest : List a) -> SnocList (input ++ rest)
snocListHelper {input} acc [] = rewrite appendNilRightNeutral input in acc
snocListHelper {input} acc (x :: xs) =
  rewrite appendAssociative input [x] xs in
    snocListHelper (Snoc acc {x}) xs

total
snocList : (xs : List a) -> SnocList xs
snocList xs = snocListHelper Empty xs

total
myReverse : List a -> List a
myReverse xs' with (snocList xs')
  myReverse []          | Empty = []
  myReverse (xs ++ [x]) | Snoc rec = x :: myReverse xs | rec

isSuffix : Eq a => List a -> List a -> Bool
isSuffix xs' ys' with (snocList xs')
  isSuffix [] ys                | Empty = True
  isSuffix (xs'' ++ [x'']) ys'' | Snoc xs_rec with (snocList ys'')
    isSuffix (xs ++ [x]) []          | Snoc xs_rec | Empty = False
    isSuffix (xs ++ [x]) (ys ++ [y]) | Snoc xs_rec | Snoc ys_rec =
      if x == y
      then isSuffix xs ys | xs_rec | ys_rec
      else False



