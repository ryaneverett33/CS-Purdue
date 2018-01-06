#include <stdio.h>
#include <stdlib.h>
#include "resize.h"

void printArray(resizableArray *array) {
	int i;
	printf("Max Size: %d, Curr Size: %d\n", array->maxSize, array->currSize);
	for (i = 0; i < array->currSize; i++) {
		printf("Index: %d, Value: %d\n", i, array->array[i]);
	}
}
int main() {
	resizableArray *array = rArrayInitialize(5);
	printArray(array);
	rArrayAdd(array,7);
	rArrayAdd(array,2);
	printArray(array);
	rArrayRemove(array,0);
	printArray(array);
	rArrayRemove(array,0);
	printArray(array);
	rArrayAdd(array,22);
	rArrayAdd(array,11);
	rArrayAdd(array,7);
	rArrayAdd(array,10);
	rArrayAdd(array,33);
	rArrayAdd(array,69);
	printArray(array);
	puts("removing");
	rArrayRemove(array,2);
	printArray(array);
	/*
	22
	11
	10
	33*/
	rArrayRemove(array,3);
	printArray(array);
	/*
	22
	11
	10*/
	rArrayRemove(array,1);
	printArray(array);
	rArrayRemove(array,0);
	rArrayRemove(array,0);
	return 1;
}