module Section2

data State : (stateType : Type) -> Type -> Type where
  Get : State stateType stateType
  Put : stateType -> State stateType ()

  Pure : ty -> State stateType ty
  Bind : State stateType a -> (a -> State stateType b) -> State stateType b

get : State stateType stateType
get = Get

put : stateType -> State stateType ()
put = Put

mutual
  Functor (State stateType) where
    map func x = do val <- x
                    pure (func val)

  Applicative (State stateType) where
    pure = Pure
    (<*>) f a = do f' <- f
                   a' <- a
                   pure (f' a')

  Monad (State stateType) where
    (>>=) = Bind

data Tree a = Empty
            | Node (Tree a) a (Tree a)

testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty)
                      "Fred"
                      (Node Empty "Sheila" Empty))
                "Alice"
                (Node Empty
                      "Bob"
                      (Node Empty "Eve" Empty))

treeLabelWith : Tree a -> State (Stream labelType) (Tree (labelType, a))
treeLabelWith Empty = pure Empty
treeLabelWith (Node left x right) =
  do left_labelled <- treeLabelWith left
     (current :: rest) <- get
     put rest
     right_labelled <- treeLabelWith right
     pure (Node left_labelled (current, x) right_labelled)

runState : State stateType a -> (st : stateType) -> (a, stateType)
runState Get st = (st, st)
runState (Put newState) st = ((), newState)
runState (Pure x) st = (x, st)
runState (Bind cmd f) st = let (val, nextState) = runState cmd st in
                               runState (f val) nextState

treeLabel : Tree a -> Tree (Integer, a)
treeLabel tree = fst $ runState (treeLabelWith tree) [1..]

addIfPositive : Integer -> State Integer Bool
addIfPositive val =
  do when (val > 0) $
          do current <- get
             put (current + val)
     pure (val > 0)

addPositives : List Integer -> State Integer Nat
addPositives xs = do added <- traverse addIfPositive xs
                     pure (length (filter id added))



