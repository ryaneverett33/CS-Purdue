all: main.c sub_string.c sub_string.s main.s
	gcc -o c2asm main.c sub_string.s
	gcc -o asm2c main.s sub_string.c

c2asm: main.c sub_string.s
	gcc -o c2asm main.c sub_string.s

asm2c: main.s sub_string.c
	gcc -o asm2c main.s sub_string.c

clean:
	rm c2asm
	rm asm2c
