#include <stdlib.h>
#include <stdio.h>

int myprintf(char* format, ...) {
	int i = 0, j = 1, argCount = 0;
	int* argPointer = &format + j;
	char curr = format[i];
	while (curr != 0) {
		if (curr == '%') {
			argCount = argCount + 1;
			char op = format[i+1];
			//printf("op=%c\n", op);
			if (op == 'c') {
				//get argument
				putchar(*argPointer);
				j = j + 1;
				argPointer = &format + j;		//increment argPointer
			}
			else if (op == 's') {
				//loop through string
				char* strPoint = *argPointer;
				int x = 0;
				j = j + 1;
				while (strPoint[x] != 0) {
					putchar(strPoint[x]);
					x = x + 1;
				}
				argPointer = &format + j;
			}
			else if (op == 'x') {
				printx(*argPointer);
				j = j + 1;
				argPointer = &format + j;
			}
			else if (op == 'd') {
				printd(*argPointer);
				j = j + 1;
				argPointer = &format + j;
			}
			else if (op == '%') {
				putchar('%');
			}
			i = i + 2;
		}
		else {
			putchar(curr);
			i = i + 1;
		}
		curr = format[i];
	}
	
}
