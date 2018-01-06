#include <stdio.h>
#include "stack.h"
#include <stdlib.h>

int top=0;		//length of the stack
double stack[MAXSTACK];
int stackLen = 0;

void stack_clear() 
{
  top = 0;
  stackLen = 0;
}

double stack_pop()
{
	// Add implementation here`
	// Be sure to check if stack is empty, using assert or otherwise, "Stack Underflow" would be the error here
	if (stackLen == 0) {
		printf("Stack underflow\n");
		exit(0);
	}
	else {
		double x = stack[top - 1];
		//printf("Pop(): %lf\n", x);
		stack[top - 1] = 0;
		stackLen--;
		top--;
		return x;
	}
}

void stack_push(double val)
{
	// Add implementation here
	// Be sure to check if stack is full, using assert or otherwise, "Stack Overflow" would be the error here
	if (stackLen == MAXSTACK) {
		printf("Stack overflow\n");
		exit(0);
	}
	else {
		//stackLen++;
		stack[stackLen] = val;
		top++;
		stackLen++;
	}
}

void stack_print()
{
	// Add implementation here
	int i;
	printf("Stack:\n");
	if (stackLen == 0) {
		printf("Stack is empty\n");
	}
	for (i = 0; i < stackLen; i++) {
		printf("%i: %f\n", i, stack[i]);
	}
}

int stack_top()
{
  return top;
}

int stack_max()
{
  return MAXSTACK;
}

int stack_is_empty()
{
  return top == 0;
}
