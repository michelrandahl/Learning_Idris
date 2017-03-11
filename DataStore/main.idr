module Main

import Data.Vect


data DataStore : Type where
  MkData : (size : Nat) -> (items : Vect size String) -> DataStore

size : DataStore -> Nat
size (MkData size' items') = size'

items : (store : DataStore) -> Vect (size store) String
items (MkData size items) = items

addToStore : DataStore -> String -> DataStore
addToStore (MkData size items) newitem =
  MkData _ (addToData items) -- <- infers the size.. coool!
  where
    addToData : (items : Vect oldsize String) -> Vect (S oldsize) String
    addToData [] = [newitem]
    addToData (x :: xs) = x :: addToData xs

data Command = Add String
             | Get Integer
             | Quit

parse : (input : String) -> Maybe Command
parse input =
  case span (/= ' ') input of
    (cmd, args) => parseCommand cmd (ltrim args)
  where
    parseCommand : (cmd : String) -> (args : String) -> Maybe Command
    parseCommand "add" str = Just (Add str)
    parseCommand "get" val =
      case all isDigit (unpack val) of
        False => Nothing
        True => Just (Get (cast val))
    parseCommand "quit" _ = Just Quit
    parseCommand _ _ = Nothing

proccessInput : DataStore -> (input : String) -> Maybe (String, DataStore)
proccessInput store input =
  case parse input of
       Nothing => Just ("Invalid command\n", store)
       Just (Add x) => Just ("ID " ++ show (size store) ++ "\n", addToStore store x)
       Just (Get x) => getEntry x store
       Just Quit => Nothing
  where
    getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
    getEntry pos store =
      let store_items = items store in
        case integerToFin pos (size store) of
           Nothing => Just ("out of range\n", store)
           Just id => Just (index id store_items ++ "\n",
                            store)

main : IO ()
main = replWith (MkData _ []) "Command: " proccessInput
