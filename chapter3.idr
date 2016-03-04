import Data.Vect

fourInts : Vect 4 Int
fourInts = [0,1,2,3]

sixInts : Vect 6 Int
sixInts = [0,1,2,3,4,5]

tenInts : Vect 10 Int
tenInts = fourInts ++ sixInts
