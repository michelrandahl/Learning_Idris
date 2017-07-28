module Section1

import Control.Monad.State

%default total

data Tree a = Empty
            | Node (Tree a) a (Tree a)

testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty) "Fred"
                      (Node Empty "Sheila" Empty)) "Alice"
                (Node Empty "Bob" (Node Empty "Eve" Empty))

flatten : Tree a -> List a
flatten Empty = []
flatten (Node x y z) = flatten x ++ y :: flatten z

treeLabelWith : (labels : Stream labelType) -> Tree a -> (Stream labelType,
                                                          Tree (labelType, a))
treeLabelWith labels Empty = (labels, Empty)
treeLabelWith labels (Node left current right) =
  let (current_label :: rem_labels, left_labelled) = treeLabelWith labels left
      (labels_right, right_labelled) = treeLabelWith rem_labels right
  in
    (labels_right, Node left_labelled (current_label, current) right_labelled)

treeLabel : Tree a -> Tree (Integer, a)
treeLabel tree = snd $ treeLabelWith [1..] tree

increase : Nat -> State Nat ()
increase inc = do current <- get
                  put (current + inc)

treeLabelWith2 : Tree a -> State (Stream labelType) (Tree (labelType, a))
treeLabelWith2 Empty = pure Empty
treeLabelWith2 (Node left x right) =
  do left_labelled <- treeLabelWith2 left
     (x_label :: rest_labels) <- get
     put rest_labels
     right_labelled <- treeLabelWith2 right
     pure (Node left_labelled (x_label, x) right_labelled)

treeLabel2 : Tree a -> Tree (Integer, a)
treeLabel2 tree = evalState (treeLabelWith2 tree) [1..]

-- exercises

update : (stateType -> stateType) -> State stateType ()
update f = do stuff <- get
              put $ f stuff

increase2 : Nat -> State Nat ()
increase2 x = update (+ x)

countEmpty : Tree a -> State Nat ()
countEmpty Empty = update (+ 1)
countEmpty (Node left x right) =
  do countEmpty left
     countEmpty right

countEmptyAndNode : Tree a -> State (Nat, Nat) ()
countEmptyAndNode Empty = do (empty_count, node_count) <- get
                             put (S empty_count, node_count)
countEmptyAndNode (Node left x right) =
  do countEmptyAndNode left
     countEmptyAndNode right
     (empty_count, node_count) <- get
     put (empty_count, S node_count)





