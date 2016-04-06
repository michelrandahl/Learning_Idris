module Main

import Data.Vect

data DataStore : Type where
  MkData : (size : Nat) -> (items : Vect size String) -> DataStore

size : DataStore -> Nat
size (MkData size' items') = size'

items : (store : DataStore) -> Vect (size store) String
items (MkData size' items') = items'

addToStore : DataStore -> String -> DataStore
addToStore (MkData size' items) newitem = MkData _ (addToData items)
  where
    addToData : Vect old String -> Vect (S old) String
    addToData [] = [newitem]
    addToData (item' :: items') = item' :: addToData items'

sumInputs : Integer -> String -> Maybe (String, Integer)
sumInputs acc inp =
  let val = cast inp in
      if val < 0 then Nothing
      else
        let newVal = acc + val in
            Just("sub total: " ++ show newVal ++ "\n", newVal)

data Command = Add String
             | Get Integer
             | Size
             | Search
             | Quit

parseCommand : (cmd : String) -> (args : String) -> Maybe Command
parseCommand "add" args = Just (Add args)
parseCommand "get" args = case all isDigit (unpack args) of
                               False => Nothing
                               True  => Just (Get (cast args))
parseCommand "size" args = Just Size
parseCommand "search" args = Just Search
parseCommand "quit" "" = Just Quit
parseCommand _ _ = Nothing

parse : (input : String) -> Maybe Command
parse input = case span (/= ' ') input of
                   (cmd, args) => parseCommand cmd (ltrim args)

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store =
  let store_items = items store in
      case integerToFin pos (size store) of
           Nothing => Just ("Out of range\n", store)
           Just id => Just (index id store_items ++ "\n", store)

showAll : (store: DataStore) -> List (Nat, String)
showAll store = loop Z (items store)
  where
    loop : Nat -> Vect _ String -> List (Nat, String)
    loop _ [] = []
    loop n (x :: xs) = (n,x) :: loop (S n) xs

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input =
  case parse input of
       Nothing => Just ("invalid cmd\n", store)
       Just (Add x) => Just ("ID" ++ show (size store) ++ "\n",
                             addToStore store x)
       Just (Get pos) => getEntry pos store
       Just Size => Just ("Size is: " ++ show (size store) ++ "\n",
                          store)
       Just Search => Just ("Elements are: " ++ show (showAll store) ++ "\n",
                            store)
       Just Quit => Nothing

main : IO()
main = replWith (MkData _ []) "Cmd: " processInput

