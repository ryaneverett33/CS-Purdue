goal: testmemdump mem

testmemdump: mymemdump.c testmemdump.c obj/orgmemdump.o
	gcc -std=gnu99 -Werror  -g -o testmemdump testmemdump.c mymemdump.c obj/orgmemdump.o

mem: mymemdump.c mem.c
	gcc -std=gnu99 -Wall -Werror -g -o mem mymemdump.c mem.c

clean:
	rm -f mem testmemdump total.* *.out
