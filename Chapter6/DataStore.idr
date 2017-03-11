module Main

import Data.Vect

infixr 5 .+.

data Schema = SString
            | SInt
            | SChar
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType SChar = Char
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
  constructor MkData
  schema : Schema
  size   : Nat
  items  : Vect size (SchemaType schema)

addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size items) newitem =
  MkData schema _ (addToData items)
  where
    addToData : Vect n (SchemaType schema) -> Vect (S n) (SchemaType schema)
    addToData [] = [newitem]
    addToData (x :: xs) = x :: addToData xs

data Command : Schema -> Type where
  SetSchema : (new_schema : Schema) -> Command schema
  Add       : SchemaType schema -> Command schema
  Get       : Integer -> Command schema
  GetAll    : Command schema
  Quit      : Command schema

parseSchema : List String -> Maybe Schema
parseSchema ("Char" :: xs) =
  case xs of
       [] => Just SChar
       _  => do
         parsed_schema <- parseSchema xs
         pure (SChar .+. parsed_schema)
parseSchema ("String" :: xs) =
  case xs of
       [] => Just SString
       _  => do
         parsed_schema <- parseSchema xs
         pure (SString .+. parsed_schema)
parseSchema ("Int" :: xs) =
  case xs of
       [] => Just SInt
       _  => do
         parsed_schema <- parseSchema xs
         pure (SInt .+. parsed_schema)
parseSchema _ = Nothing

parsePrefix : (schema : Schema) -> (input : String) -> Maybe (SchemaType schema, String)
parsePrefix SChar input =
  case (unpack input) of
       [] => Nothing
       char :: rest_input => Just (char, ltrim (pack rest_input))
parsePrefix SString input = getQuoted (unpack input)
  where
    getQuoted : List Char -> Maybe (String, String)
    getQuoted ('"' :: xs) =
      case span (/= '"') xs of
           (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
           _ => Nothing
    getQuoted _ = Nothing
parsePrefix SInt input =
  case span isDigit input of
       ("", rest) => Nothing
       (num, rest) => Just (cast num, ltrim rest)
parsePrefix (schemaLeft .+. schemaRight) input = do
  (left_val, rest_of_input)   <- parsePrefix schemaLeft input
  (right_val, rest_of_input') <- parsePrefix schemaRight rest_of_input
  pure ((left_val, right_val), rest_of_input')

parseBySchema : (schema : Schema) -> (input : String) -> Maybe (SchemaType schema)
parseBySchema schema input = do
  (parsed_result, rest) <- parsePrefix schema input
  if rest == ""
  then pure parsed_result
  else Nothing

parseCommand : (schema : Schema) -> (cmd : String) -> (args : String) -> Maybe (Command schema)
parseCommand schema "add" rest = do
  parsed_result <- parseBySchema schema rest
  pure (Add parsed_result)
parseCommand schema "get" val =
  if val == ""
  then Just GetAll
  else
    case all isDigit (unpack val) of
         False => Nothing
         True  => Just (Get (cast val))
parseCommand schema "quit" "" = Just Quit
parseCommand schema "schema" rest = do
  parsed_schema <- parseSchema (words rest)
  pure (SetSchema parsed_schema)
parseCommand _ _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input =
  case span (/= ' ') input of
       (cmd, args) => parseCommand schema cmd (ltrim args)

display : SchemaType schema -> String
display {schema = SString}   x      = show x
display {schema = SInt}      x      = show x
display {schema = SChar}     x      = show x
display {schema = (x .+. y)} (a, b) =
  display a ++ ", " ++ display b

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store =
  let store_items = items store in
      case integerToFin pos (size store) of
           Nothing => Just ("out of range\n", store)
           Just id => Just (display (index id store_items) ++ "\n", store)

setSchema : (store : DataStore) -> (schema : Schema) -> Maybe DataStore
setSchema store schema =
  case size store of
       Z => Just (MkData schema _ [])
       S k => Nothing

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input =
  case parse (schema store) input of
       Nothing => Just ("Invalid cmd\n", store)
       Just (SetSchema schema) =>
         case setSchema store schema of
              Nothing => Just ("cant update schema\n", store)
              Just store => Just ("schema updated!\n", store)
       Just (Add x) => Just ("ID" ++ show (size store) ++ "\n",
                             addToStore store x)
       Just (Get x) => getEntry x store
       Just GetAll => Just (showAll store, store)
       Just Quit => Nothing
  where
    showAll : (store : DataStore) -> String
    showAll store = foldl (\acc,elem => acc ++ display elem ++ "\n") "" (items store)

main : IO ()
main = replWith (MkData (SString .+. SInt) _ [])
                "Command: "
                processInput


