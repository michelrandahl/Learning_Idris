module InteractiveShell

%default total

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String
  ReadFile : (path : String) -> Command (Either FileError String)
  WriteFile : (path : String) -> (contents : String) -> Command (Either FileError ())

  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleIODo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand (ReadFile path) = readFile path
runCommand (WriteFile path contents) = writeFile path contents
runCommand (Pure x) = pure x
runCommand (Bind a f) = do res <- runCommand a
                           runCommand $ f res

data ShellCmd = Cat String
              | Copy String String
              | Exit

readInput : Command (Maybe ShellCmd)
readInput =
  do PutStr "-$: "
     input <- GetLine
     Pure $ parse input
  where
    parseInputs : (inputs : List String) -> Maybe ShellCmd
    parseInputs ["exit"] = Just Exit
    parseInputs ["copy", source, destination] = Just $ Copy source destination
    parseInputs ["cat", source] = Just $ Cat source
    parseInputs _ = Nothing

    parse : (input : String) -> Maybe ShellCmd
    parse input = parseInputs $ Strings.split (== ' ') input

data Fuel = Dry
          | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

run : Fuel -> ConsoleIO a -> IO (Maybe a)
run _ (Quit x) = pure (Just x)
run Dry _ = pure Nothing
run (More fuel) (Do a f) = do res <- runCommand a
                              run fuel $ f res

mutual
  copy : (source : String) -> (destination : String) -> ConsoleIO ()
  copy source destination =
    do result <- ReadFile source
       case result of
            Left error => PutStr $ show error ++ "\n"
            Right contents => do result <- WriteFile destination contents 
                                 case result of
                                      Left error => PutStr $ show error ++ "\n"
                                      Right () => PutStr "success!\n"
       interactiveShell

  cat : (source : String) -> ConsoleIO ()
  cat source =
    do result <- ReadFile source
       case result of
            Left file_error => PutStr $ show file_error ++ "\n"
            Right contents => PutStr $ contents ++ "\n"
       interactiveShell

  invalidCmd : ConsoleIO ()
  invalidCmd = do PutStr "invalid command!...\n"
                  interactiveShell

  interactiveShell : ConsoleIO ()
  interactiveShell = do cmd <- readInput
                        case cmd of
                             Nothing => invalidCmd
                             Just Exit => Quit ()
                             Just (Cat s) => cat s
                             Just (Copy s d) => copy s d

partial
main : IO ()
main = do res <- run forever interactiveShell
          pure ()


