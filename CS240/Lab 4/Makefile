
all: toascii countlines towords test_stack rpncalc

toascii: toascii.c
	gcc -Wall -Werror -g -o toascii toascii.c

countlines: countlines.c
	gcc -Wall -Werror -g -o countlines countlines.c

towords: towords.c
	gcc -Wall -Werror -g -o towords nextword.c towords.c	

test_stack: stack.c
	gcc -Wall -Werror -g -o test_stack stack.c test_stack.c

rpncalc: rpn.c
	gcc -Wall -Werror -g -lm -o rpncalc stack.c rpn.c rpncalc.c

clean:
	rm -f countlines towords test_stack rpncalc *out
