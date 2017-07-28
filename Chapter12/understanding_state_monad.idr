module Understanding

data State : (stateType : Type) -> Type -> Type where
  Get : State stateType stateType
  Put : stateType -> State stateType ()

  Pure : ty -> State stateType ty
  Bind : State stateType a -> (a -> State stateType b) -> State stateType b

runState : State stateType a -> (st : stateType) -> (a, stateType)
runState Get st = (st, st)
runState (Put newState) st = ((), newState)
runState (Pure x) st = (x, st)
runState (Bind cmd f) st = let (val, nextState) = runState cmd st in
                             runState (f val) nextState

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

-- unfolded version of function defined in section2
treeLabelWith : Tree a -> State (Stream l) (Tree (l, a))
treeLabelWith Empty = Pure Empty
treeLabelWith (Node left x right) =
  (Bind (treeLabelWith left) (\left_labelled =>
  (Bind Get (\xs' =>
  let (current :: rest) = xs' in
  Bind (Put rest) (\_ =>
  Bind (treeLabelWith right) (\right_labelled =>
  Pure (Node left_labelled
             (current, x)
             right_labelled)))))))

labelledTree : Tree (Integer, String)
labelledTree = fst $ runState (treeLabelWith testTree) [1..]


