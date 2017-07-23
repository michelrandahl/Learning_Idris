module Main

import Data.List.Views

total
mergeSort : Ord a => List a -> List a
mergeSort xs' with (splitRec xs')
  mergeSort []                | SplitRecNil = []
  mergeSort [x]               | SplitRecOne = [x]
  mergeSort (lefts ++ rights) | SplitRecPair lrec rrec =
    merge (mergeSort lefts | lrec)
          (mergeSort rights | rrec)


