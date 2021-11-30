module ElemType

data Vect : Nat -> Type -> Type where
     Nil  : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

data Tree : a -> Type where
  EmptyTree : Tree a
  Node : a -> Tree a -> Tree a -> Tree a

Eq a => Eq (Tree a) where
  (==) EmptyTree EmptyTree = True
  (==) (Node e l r) (Node e' l' r') =
    l == l' && e == e' && r == r'
  (==) _ _ = False


singleton : a -> Tree a
singleton x = Node x EmptyTree EmptyTree

treeInsert : Ord a => a -> Tree a -> Tree a
treeInsert e EmptyTree  = singleton e
treeInsert x (Node e l r) =
  case compare x e of
       EQ => Node x l r
       LT => Node e (treeInsert x l) r
       GT => Node e l (treeInsert x r)

nums : List Nat
nums = [8, 4, 1, 3, 7, 6, 1]

numsTree : Tree Nat
numsTree = foldr treeInsert EmptyTree nums

data Elem : a -> Vect k a -> Type where
  Here  : Elem x (x :: xs)
  There : (later : Elem x xs) -> Elem x (y :: xs)


notInNil : Elem value [] -> Void
notInNil Here impossible
notInNil (There _) impossible

notInTail : (notHere : (value = x) -> Void) ->
            (notThere : Elem value xs -> Void) ->
            Elem value (x :: xs) ->
            Void
notInTail notHere notThere Here = notHere Refl
notInTail notHere notThere (There later) = notThere later

isElem : DecEq a => (value : a) -> (xs : Vect n a) -> Dec (Elem value xs)
isElem value [] = No notInNil
isElem value (x :: xs) =
  case decEq value x of
       Yes Refl   => Yes Here
       No notHere => case isElem value xs of
                         Yes prf => Yes (There prf)
                         No notThere => No (notInTail notHere notThere)

