module state_chapter

-- to load Idris repl with effects library
-- $ idris -p effects

import Effects
import Effect.State
-- import Effect.StdIO

data BTree a = Leaf
             | Node (BTree a) a (BTree a)

testTree : BTree String
testTree = Node (Node Leaf "Jim" Leaf)
           "Fred"
           (Node (Node Leaf "Alice" Leaf)
                 "Sheila"
                 (Node Leaf "Bob" Leaf))

treeTagAux : (i : Int) -> BTree a -> (Int, BTree (Int, a))
treeTagAux i Leaf = (i, Leaf)
treeTagAux i (Node l x r) =
  let (i', l') = treeTagAux i l in
      let x' = (i', x) in
          let (i'', r') = treeTagAux (i' + 1) r in
              (i'', Node l' x' r')

treeTag : (i : Int) -> BTree a -> BTree (Int, a)
treeTag i x = snd (treeTagAux i x)

treeTagAux2 : BTree a -> Eff (BTree (Int, a)) [STATE Int]
treeTagAux2 Leaf = pure Leaf
treeTagAux2 (Node l x r) =
  do l' <- treeTagAux2 l
     i <- get
     put (i + 1)
     r' <- treeTagAux2 r
     pure (Node l' (i, x) r')

treeTag2 : (i : Int) -> BTree a -> BTree (Int, a)
treeTag2 i x = runPure (
  do put i
     treeTagAux2 x)

treeTag2a : (i : Int) -> BTree a -> BTree (Int, a)
treeTag2a i x = runPureInit [i] (treeTagAux2 x)

treeTagAux3 : BTree a -> Eff (BTree (Int, a)) ['Tag ::: STATE Int, 'Leaves ::: STATE Int]
treeTagAux3 Leaf = do 'Leaves :- update (+1)
                      pure Leaf
treeTagAux3 (Node l x r) = do l' <- treeTagAux3 l
                              i <- 'Tag :- get
                              'Tag :- put (i + 1)
                              r' <- treeTagAux3 r
                              pure (Node l' (i, x) r')

treeTag3 : (i : Int) -> BTree a -> (Int, BTree (Int, a))
treeTag3 i x = runPureInit ['Tag := i, 'Leaves := 0]
                           (do x' <- treeTagAux3 x
                               leaves <- 'Leaves :- get
                               pure (leaves, x'))


stateLength : Eff Nat [STATE String]
stateLength = pure (length !get)


