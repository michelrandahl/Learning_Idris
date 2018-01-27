compile shared lib file
$ gcc -o hello.o -c hello.c
$ gcc -shared -o libhello.so hello.o -lm
