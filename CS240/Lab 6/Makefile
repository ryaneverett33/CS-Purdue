main: main.c io.c hashtable.c linkedlist.c
	gcc -Wall -Werror hash.o hashtable.c linkedlist.c io.c main.c -o process

io_test: io.c io_test.c
	gcc -Wall hash.o hashtable.c linkedlist.c io.c io_test.c -o io_test

hash_test: hashtable.c hash_test.c
	gcc -Wall hash.o hashtable.c hash_test.c -o hash_test
	gcc -Wall hash.o hashtable.c Hashsize_test.c -o Hashsize
	
list_test: linkedlist.c list_test.c empty_test.c
	gcc -Wall linkedlist.c list_test.c -o list_test
	gcc -Wall linkedlist.c empty_test.c -o empty_test

