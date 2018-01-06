#include <stdio.h>
#include <stdlib.h>
#include "stack.h"

struct stack *newStack(int max_size) {
	struct stack *newStack = malloc(sizeof(struct stack));
	newStack->max_size = max_size;
	newStack->top = -1;
	newStack->contents = malloc(sizeof(struct item) * max_size);
	
	return newStack;
}

int push(struct stack * s, double value, int (*callback)()) {
	if (s == NULL || callback == NULL) {
		return -1;
	}
	struct item *newItem = malloc(sizeof(struct item));
	newItem->value = value;
	newItem->callback = callback;
	
	if (s->top != (s->max_size - 1)) {
		s->top++;
		s->contents[s->top] = newItem;
	}
	else {
		free (newItem);
		return -1;
	}
	return 0;
}

double popAndCall(struct stack * s) {
	if (s == NULL || s->top == -1) {
		return 0;
	}
	int top = s->top;
	printf("pop(): top is %d\n", top);
	double value = s->contents[s->top]->value;
	s->contents[s->top]->callback();
	free(s->contents[s->top]);
	s->contents[s->top] = NULL;
	s->top--;
	return value;
}