%dynamic "/home/michel/Documents/Learning_Idris/foreign-fun/hello-c/hello.so"

hello_c : IO ()
hello_c = foreign FFI_C "hello" (IO ())
