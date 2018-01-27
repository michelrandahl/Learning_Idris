import Data.So
import Data.Vect

foobar : So (1 < 2)
foobar = Oh

IsLte : Ord e => (x : e) -> (y : e) -> Type
IsLte x y = So $ x <= y

-- *IsLte> the (IsLte 1 2) Oh
-- Oh : So True

-- *IsLte> the (IsLte 2 1) Oh
-- unification error

mkIsLte : Ord e => (x : e) -> (y : e) -> Maybe (IsLte x y)
mkIsLte x y =
  case choose $ x <= y of
       Left prf  => Just prf 
       Right prf => Nothing

-- proof that and element is head of vector
data HeadIs : Vect n e -> e -> Type where
  MkHeadIs : HeadIs (x :: xs) x

data IsSorted : (xs : Vect n e) -> Type where
  IsSortedZero : IsSorted []
  IsSortedOne  : Ord e => (x : e) -> IsSorted (x :: Nil)
  IsSortedMany : Ord e =>
                 -- for the variables...
                 (x : e) -> (y : e) -> (ys : Vect n'' e) ->
                 -- if x is less than y...
                 (IsLte x y) ->
                 -- and (y :: ys) is sorted...
                 IsSorted (y :: ys) ->
                 -- then the whole vector must be sorted...
                 IsSorted (x :: (y :: ys))

mkIsSorted : Ord e => (xs : Vect n e) -> Maybe (IsSorted xs)
mkIsSorted [] = Just IsSortedZero
mkIsSorted (x :: []) = Just (IsSortedOne x)
mkIsSorted (x :: (y :: xs)) =
  case (mkIsLte x y) of
       Nothing => Nothing
       Just x_lte_y =>
         case (mkIsSorted (y::xs)) of
              Nothing => Nothing
              Just y_xs_isSorted =>
                Just (IsSortedMany x y xs x_lte_y y_xs_isSorted)


mkIsSorted2 : Ord e => (xs : Vect n e) -> Maybe (IsSorted xs)
mkIsSorted2 [] = Just IsSortedZero
mkIsSorted2 (x :: []) = Just (IsSortedOne x)
mkIsSorted2 (x :: (y :: xs)) =
  do x_lte_y <- mkIsLte x y
     y_xs_isSorted <- mkIsSorted2 (y :: xs)
     pure $ IsSortedMany x y xs x_lte_y y_xs_isSorted


