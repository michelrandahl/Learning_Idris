module TestStore

import DataStore

testStore : DataStore (SString .+. SString .+. SInt)
testStore = addToStore ("Mercury", "Mariner 10", 1974)
          $ addToStore ("Venus", "Venera", 1961)
          $ addToStore ("Uranus", "Voyager 2", 1986)
          $ addToStore ("Pluto", "New Horizons", 2015)
          $ empty

total
listItems : DataStore schema -> List (SchemaType schema)
listItems x' with (storeView x')
  listItems x                        | SNil = []
  listItems (addToStore value store) | (SAdd rec) =
    value :: listItems store | rec

total
filterKeys : (predicate : SchemaType val_schema -> Bool) -> DataStore (SString .+. val_schema) -> List String
filterKeys predicate x' with (storeView x')
  filterKeys predicate x                               | SNil = []
  filterKeys predicate (addToStore (key, value) store) | SAdd rec =
    if predicate value
    then key :: filterKeys predicate store | rec
    else filterKeys predicate store | rec

-- exercises
getValues : DataStore (SString .+. val_schema) -> List (SchemaType val_schema)
getValues x' with (storeView x')
  getValues x                              | SNil = []
  getValues (addToStore (key,value) store) | (SAdd rec) =
    value :: getValues store

testStore2 : DataStore (SString .+. SInt)
testStore2 = addToStore ("First", 1)
           $ addToStore ("Second", 2)
           $ empty



