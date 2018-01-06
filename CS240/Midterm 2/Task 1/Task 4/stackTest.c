#include <stdio.h>
#include <stdlib.h>
#include "stack.h"

int callback() {
	puts("Got a callback");
	return 0;
}
void printStack(struct stack *foo) {
	int max_size = foo->max_size, top = foo->top;
	printf("Top index: %d, Max Size: %d\n", top, max_size);
	if (top == (max_size - 1)) {
		puts("Stack is full");
	}
	else if (top == -1) {
		puts("Stack is empty");
	}
	else {
		puts("Stack is not full");
	}
	int i;
	for (i = 0; i <= top; i++) {
		double value = foo->contents[i]->value;
		printf("%d: %lf\n", i, value);
	}
}
void freeStack(struct stack *foo) {
	int i;
	for (i = 0; i < foo->max_size; i++) {
		if (foo->contents[i] != NULL) {
			free(foo->contents[i]);
		}
	}
	free(foo->contents);
	free(foo);
}
int main() {
	struct stack *newerStack = newStack(5);
	printStack(newerStack);
	int x = push(newerStack, 5.0, callback);
	if (x != 0) {
		puts("failed to push item");
	}
	printStack(newerStack);
	if (push(newerStack, 12.0, callback) != 0) {
		puts("failed to push item");
	}
	printf("Popped value = %lf\n", popAndCall(newerStack));
	printStack(newerStack);
	popAndCall(newerStack);
	freeStack(newerStack);
	struct stack *stack2 = newStack(2);
	push(stack2,1.0,callback);
	push(stack2, 2.0, callback);
	if (push(stack2, 3.0, callback) != 0) {
		puts("cannot push 3.0");
	}
	popAndCall(stack2);
	popAndCall(stack2);
	freeStack(stack2);
	return 1;
}