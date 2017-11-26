import ProcessLib

record WCData where
  constructor MkWCData
  wordCount : Nat
  lineCount : Nat

doCount : (content : String) -> WCData
doCount content = let line_count = length (lines content)
                      word_count = length (words content) in
                      MkWCData word_count line_count

data WC = CountFile String
        | GetData String

WCType : WC -> Type
WCType (CountFile x) = ()
WCType (GetData x) = Maybe WCData

countFile : (files : List (String, WCData)) -> (file_name : String) -> Process WCType (List (String, WCData)) Sent Sent
countFile files file_name =
  do Right content <- Action (readFile file_name) | _ => Pure files
     Action $ putStrLn ("counting complete for " ++ file_name)
     Pure $ (file_name, doCount content) :: files

wcService : (loaded : List (String , WCData)) -> Service WCType ()
wcService loaded = do msg <- Respond (\msg => case msg of
                                                   CountFile x => Pure ()
                                                   GetData x => Pure $ lookup x loaded)
                      newLoaded <- case msg of
                                        Just (CountFile file_name) => countFile loaded file_name
                                        _ => Pure loaded
                      Loop (wcService newLoaded)

procMain : Client ()
procMain = do Just wc <- Spawn (wcService []) | _ => Action (putStrLn "spawn failed")
              Action ( putStrLn "counting test.txt" )
              Request wc (CountFile "test.txt")
              Action ( putStrLn "processing" )
              Just wc_data <- Request wc (GetData "test.txt") | _ => Action (putStrLn "file error")
              Action $ putStrLn ("words: " ++ show (wordCount wc_data))
              Action $ putStrLn ("lines: " ++ show (lineCount wc_data))

