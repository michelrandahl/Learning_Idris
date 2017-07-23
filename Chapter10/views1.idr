module Main

data ListLast : List a -> Type where
  Empty : ListLast []
  NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

test1 : ListLast []
test1 = Empty

test2 : ListLast ([1, 2] ++ [3])
test2 = NonEmpty [1,2] 3

total
listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) =
  case listLast xs of
       Empty => NonEmpty [] x
       NonEmpty ys y => NonEmpty (x :: ys) y

describeListEnd : List Int -> String
describeListEnd input with (listLast input)
  describeListEnd []          | Empty = "Empty"
  describeListEnd (xs ++ [x]) | NonEmpty xs x =
    "Non-empty, initial portion = " ++ show xs

-- non-total and inefficient reverse function
myReverse : List a -> List a
myReverse xs with (listLast xs)
  myReverse []          | Empty = []
  myReverse (ys ++ [y]) | NonEmpty ys y = y :: myReverse ys

data SplitList : List a -> Type where
  SplitNil  : SplitList []
  SplitOne  : SplitList [x]
  SplitPair : (lefts : List a) -> (rights : List a) -> SplitList (lefts ++ rights)


total
splitList : (input : List a) -> SplitList input
splitList input = splitListHelp input input
  where
    splitListHelp : List a -> (input : List a) -> SplitList input
    splitListHelp _ [] = SplitNil
    splitListHelp _ [x] = SplitOne
    splitListHelp (_ :: _ :: counter) (y :: ys) =
      case splitListHelp counter ys of
           SplitNil               => SplitOne
           SplitOne {x}           => SplitPair [y] [x]
           SplitPair lefts rights => SplitPair (y :: lefts) rights
    splitListHelp _ xs = SplitPair [] xs

mergeSort : Ord a => List a -> List a
mergeSort xs with (splitList xs)
  mergeSort []                | SplitNil = []
  mergeSort [x]               | SplitOne = [x]
  mergeSort (lefts ++ rights) | SplitPair lefts rights =
    merge (mergeSort lefts) (mergeSort rights)

