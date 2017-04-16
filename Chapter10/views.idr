module Views

describeList : List Int -> String
describeList [] = "Empty"
describeList (x :: xs) = "Non-empty, tail = " ++ show xs

-- ListLast is a view that enables pattern matching at the end of a list
data ListLast : List a -> Type where
  Empty : ListLast []
  NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

describeHelper : (input : List Int) -> (form : ListLast input) -> String
describeHelper [] Empty = "Empty"
describeHelper (xs ++ [x]) (NonEmpty xs x) =
  "Non-empty, initial portion = " ++ show xs

-- listLast is a covering function of the ListLast view
total
listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) =
  case listLast xs of
       Empty => NonEmpty [] x
       NonEmpty ys y => NonEmpty (x :: ys) y

describeListEnd : List Int -> String
describeListEnd xs = describeHelper xs (listLast xs)

-- defining describeListEnd without the helper, using extended pattern matching 'with blocks'
describeListEnd2 : List Int -> String
describeListEnd2 input with (listLast input)
  describeListEnd2 []          | Empty = "Empty"
  describeListEnd2 (xs ++ [x]) | NonEmpty xs x =
    "Non-empty, initial portion = " ++ show xs

-- inefficient reverse function, and Idris can't figure out if its total :(
myReverse : List a -> List a
myReverse xs with (listLast xs) -- listLast is called on every recursion, not good :(
  myReverse []           | Empty = []
  myReverse (xs' ++ [x]) | NonEmpty xs' x =
    x :: myReverse xs'

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
    splitListHelp (_ :: _ :: counter) (item :: items) =
      case splitListHelp counter items of
           SplitNil => SplitOne
           SplitOne {x} => SplitPair [item] [x]
           SplitPair lefts rights => SplitPair (item :: lefts) rights
    splitListHelp _ items = SplitPair [] items

-- Idris still can't figure out if the function is total
mergeSort : Ord a => List a -> List a
mergeSort xs with (splitList xs)
  mergeSort []                | SplitNil = []
  mergeSort [x]               | SplitOne = [x]
  mergeSort (lefts ++ rights) | SplitPair lefts rights =
    merge (mergeSort lefts) (mergeSort rights)


-- Exercises
data TakeN : List a -> Type where
  Fewer : TakeN xs
  Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)

total
takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z xs = Exact []
takeN (S k) [] = Fewer
takeN (S k) (x :: xs) with (takeN k xs)
  takeN (S k) (x :: xs)             | Fewer = Fewer
  takeN (S k) (x :: n_xs ++ rest)   | (Exact n_xs) = Exact (x :: n_xs)

groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs             | Fewer = [xs]
  groupByN n (n_xs ++ rest) | Exact n_xs = n_xs :: groupByN n rest



