module Main

parseInt : String -> Maybe Int
parseInt x =
  if all isDigit $ unpack x
     then Just $ cast x
     else Nothing

confirmAge : IO Bool
confirmAge = do putStrLn "how old are you?"
                input <- getLine
                let age = parseInt (trim input)
                case age of
                     Nothing => do putStrLn "didn't understand, come again..."
                                   confirmAge
                     Just x => pure (if x >= 18
                                        then True
                                        else False)


adultsOnly : IO (Provider Bool)
adultsOnly =
  do oldEnough <- confirmAge
     if oldEnough
        then do putStrLn "ok"
                pure (Provide True)
        else pure (Error "only adults may compile this program")

%provide (ok : Bool) with adultsOnly

main : IO ()
main = do putStrLn "secret message!!!"
