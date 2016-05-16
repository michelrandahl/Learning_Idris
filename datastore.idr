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
  schema: Schema
  size: Nat
  items: Vect size (SchemaType schema)

data Command : Schema -> Type where
  SetSchema : (new_schema: Schema) -> Command schema
  Add    : SchemaType schema -> Command schema
  Get    : Integer -> Command schema
  GetAll : Command schema
  Quit   : Command schema



addToStore : (store: DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size store) newitem =
  MkData schema _ (addToData store)
  where
    addToData : Vect old_size (SchemaType schema) ->
                Vect (S old_size) (SchemaType schema)
    addToData [] = [newitem]
    addToData (item' :: items') = item' :: addToData items'



parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)

parsePrefix SString input = getQuoted (unpack input)
  where
    getQuoted : List Char -> Maybe (String, String)
    getQuoted ('"' :: xs) =
      case span (/= '"') xs of
           (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
           ____________________  => Nothing
    getQuoted _ = Nothing

parsePrefix SInt input =
  case span isDigit input of
       ("", rest) => Nothing
       (num, rest) => Just (cast num, ltrim rest)

parsePrefix SChar input =
  case unpack input of
       []      => Nothing
       x :: xs => Just (x, ltrim $ pack xs)

parsePrefix (schema_left .+. schema_right) input =
  do (left_val, input') <- parsePrefix schema_left input
     (right_val, input'') <- parsePrefix schema_right input'
     Just ( (left_val, right_val), input'' )



parseBySchema : (schema : Schema) -> String -> Maybe (SchemaType schema)
parseBySchema schema input =
  case parsePrefix schema input of
       Just (res, "") => Just res
       Just _         => Nothing
       Nothing        => Nothing



parseSchema : List String -> Maybe Schema

parseSchema ("String" :: xs) =
  case xs of
       [] => Just SString
       _ => do xs_schema <- parseSchema xs
               Just (SString .+. xs_schema)

parseSchema ("Int" :: xs) =
  case xs of
       [] => Just SInt
       _ => do xs_schema <- parseSchema xs
               Just (SInt .+. xs_schema)

parseSchema ("Char" :: xs) =
  case xs of
       [] => Just SChar
       _ => do xs_schema <- parseSchema xs
               Just (SChar .+. xs_schema)

parseSchema _ = Nothing



parseCommand : (schema : Schema) -> String -> String -> Maybe (Command schema)

parseCommand schema "add" rest =
  do rest_ok <- parseBySchema schema rest
     Just (Add rest_ok)

parseCommand schema "get" arg =
  case (all isDigit (unpack arg), arg) of
       (False, _) => Nothing
       (_, "")    => Just GetAll
       (True, _)  => Just (Get (cast arg))

parseCommand schema "quit" "" = Just Quit

parseCommand schema "schema" rest =
  do schema_ok <- parseSchema (words rest)
     Just (SetSchema schema_ok)

parseCommand _ _ _ = Nothing



display : SchemaType schema -> String
display {schema = SString} item = item
display {schema = SInt} item = show item
display {schema = SChar} item = show item
display {schema = (x .+. y)} (a, b) = display a ++ ", " ++ display b



parse : (schema: Schema) -> (input: String) -> Maybe (Command schema)
parse schema input =
  case span (/= ' ') input of
       (cmd, args) => parseCommand schema cmd (ltrim args)



getEntry : (pos: Integer) -> (store: DataStore) -> Maybe (String, DataStore)
getEntry pos store =
  let store_items = items store in
      case integerToFin pos (size store) of
           Nothing => Just ("out of range\n", store)
           Just id => Just (display (index id (items store)) ++ "\n", store)



getEntries : (store: DataStore) -> Maybe (String, DataStore)
getEntries store =
  case size store of
       Z => Nothing
       _ => let items_strings = map display (items store) in
                Just (foldl (\a,e => a ++ e ++ "\n") "" items_strings, store)



setSchema : (store: DataStore) -> Schema -> Maybe DataStore
setSchema store schema = case size store of
                              Z => Just (MkData schema _ [])
                              S k => Nothing



processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input =
  case parse (schema store) input of
       Nothing => Just ("Invalid cmd\n", store)
       Just (Add item) => Just ("ID " ++ show (size store) ++ "\n",
                                addToStore store item)
       Just (SetSchema schema') =>
        case setSchema store schema' of
             Nothing => Just ("Can't update schema\n", store)
             Just store' => Just ("OK\n", store')
       Just GetAll => getEntries store
       Just (Get pos) => getEntry pos store
       Just Quit => Nothing



main : IO ()
main = replWith (MkData (SString .+. SString .+. SInt) _ [])
                "cmd: " processInput

