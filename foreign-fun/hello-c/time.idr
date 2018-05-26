module Time

getUnixEpoch : IO Int
getUnixEpoch = foreign FFI_C "#(unsigned long)time(NULL)" (IO Int)
--getUnixEpoch = foreign FFI_C "#INT_MAX" (IO Int)

main : IO ()
main = do time <- getUnixEpoch
          putStrLn $ cast time
