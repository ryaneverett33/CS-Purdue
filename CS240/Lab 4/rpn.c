#define true 1
#define false 0

#include <string.h>
#include <stdio.h>
#include <errno.h>
#include <stdlib.h>
#include <math.h>

#include "rpn.h"
#include "nextword.h"
#include "stack.h"

//replace all x in line with argument
double rpn_eval(char * fileName, double x) {
	char word[200];
	int wordLen = 0;
	char c = 0;
	FILE * fd = fopen(fileName, "r");
	int space = false;
	int operating = false;

	if (fd == NULL) {
		printf("Could not open file!\n");
		return 0;
	}
	while((c = fgetc(fd)) && c != EOF) {
		//printf("while() c: %c and %d\n", c, (int)c);
		if ((c == ' ' || c == '\n')) {
			if (space || wordLen == 0) {
				continue;	
			}
			//printf("spacing\n");
			word[wordLen] = '\0';
			double tmp;
			sscanf(word, "%lf", &tmp);
			stack_push(tmp);
			wordLen = 0;
			word[0] = '\0';
			space = true;
			operating = false;
		}
		else if (c == '+') {
			double x1 = stack_pop();
			double y1 = stack_pop();
			double z1 = x1 + y1;
			//printf("%lf + %lf = %lf\n", x1, y1, z1);
			stack_push(z1);
		}
		else if (c == '-') {
			char tmp = fgetc(fd);
			if (tmp != ' ' && tmp != '\n') {
				//no space, is negative
				word[wordLen] = '-';
				wordLen++;
				word[wordLen] = tmp;
				wordLen++;
				space = false;
			}
			else {
				double x1 = stack_pop();
				double y1 = stack_pop();
				double z1 = y1 - x1;
				//printf("%lf - %lf = %lf\n", y1, x1, z1);
				stack_push(z1);
			}	
		}
		else if (c == '*') {
			double x1 = stack_pop();
			double y1 = stack_pop();
			double z1 = x1 * y1;
			//printf("%lf * %lf = %lf\n", x1, y1, z1);
			stack_push(z1);
		}
		else if (c == '/') {
			double x1 = stack_pop();
			double y1 = stack_pop();
			double z1 = y1 / x1;
			//printf("%lf div %lf = %lf\n", y1, x1, z1);
			stack_push(z1);
		}
		else if (c == 'x' && operating == false) {
			stack_push(x);
		}
		else {
			//check for operators
			if ((int)c > 64) {
				//printf("checking for operating\n");
				word[wordLen] = c;
				wordLen++;
				operating = true;

				//printf("word: %s, len: %d, c: %c\n", word, wordLen, c);
				//operator = true;
				if (wordLen >= 3 || (c == ' ' || c == '\n')) {
					//Evaluate operator
					word[3] = '\0';
					char * op = malloc(200);
					//printf("evaluating operator\n");
					sscanf(word, "%s", op);
					//printf("Operator is: %s\n", op);
					if (strcmp(word, "sin") == 0) {
						//printf("Sinning it\n");
						double x1 = stack_pop();
						stack_push(sin(x1));
						//printf("sin(%lf) = %lf\n", x1, sin(x1));
						word[0] = '\0';
						wordLen = 0;
						continue;
					}
					else if (strcmp(word, "cos") == 0) {
						//printf("Cossing it\n");
						double x1 = stack_pop();
						//printf("cos(%lf) = %lf\n", x1, cos(x1));
						stack_push(cos(x1));
						wordLen = 0;
						word[0] = '\0';
						continue;
					}
					else if (strcmp(word, "pow") == 0) {
						//printf("powering it\n");
						double x1 = stack_pop();
						double y1 = stack_pop();
						//printf("pow(%lf, %lf) = %lf\n", x1, y1, pow(x1,y1)); 
						stack_push(pow(y1,x1));
						wordLen = 0;
						word[0] = '\0';
						continue;
					}
					else if (strcmp(word, "log") == 0) {
						//printf("natural log\n");
						double x1 = stack_pop();
						stack_push(log(x1));
						//printf("log(%lf) = %lf\n", x1, log(x1));
						wordLen = 0;
						word[0] = '\0';
						continue;
					}
					else if (strcmp(word, "exp") == 0) {
						//printf("exponent\n");
						double x1 = stack_pop();
						stack_push(exp(x1));
						//printf("exp(%lf) = %lf\n", x1, exp(x1));
						wordLen = 0;
						word[0] = '\0';
						continue;
					}
					else {
						continue;	
					}
				}
			}
			else {
				operating = false;
				word[wordLen] = c;
				wordLen++;
				space = false;
			}
		}
	}
	if (stack_top() != 1) {
		printf("Elements remain in the stack\n");
		exit(1);
	}
	return stack_pop();
}

