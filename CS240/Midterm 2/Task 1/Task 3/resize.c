#include <stdio.h>
#include <stdlib.h>
#include "resize.h"

resizableArray* rArrayInitialize(int maxSize) {
	resizableArray* rArray = malloc(sizeof(resizableArray));
	if (rArray == NULL) {
		return NULL;
	}
	rArray->array = malloc(sizeof(int) * 0);
	rArray->currSize = 0;
	rArray->maxSize = maxSize;
	return rArray;
}

int rArrayAdd(resizableArray *rArray, int x) {
	if (rArray == NULL) {
		return -1;
	}
	if (rArray->currSize == 0) {
		//empty, allocate space
		rArray->array = malloc(sizeof(int));
		if (rArray->array == NULL) {
			puts("alloc failed");
			return -1;
		}
		rArray->array[0] = x;
		rArray->currSize++;
		return 0;
	}
	else if (rArray->currSize < rArray->maxSize) {
		rArray->array = realloc(rArray->array, sizeof(int) * (rArray->currSize + 1));
		if (rArray->array == NULL) {
			puts("realloc failed");
			return 0;
		}
		rArray->array[rArray->currSize] = x;
		rArray->currSize++;
	}
	else if (rArray->currSize == rArray->maxSize) {
		puts("Array is full, can't add.");
		return -1;
	}
	return -1;
}
int rArrayRemove(resizableArray *rArray, int i) {
	if (rArray == NULL) {
		return -1;
	}
	if (rArray->currSize == 0) {
		puts("Array is empty, cannot remove");
		return 0;
	}
	//Array is not empty, treat remove
	else {
		if (i < 0 || i >= rArray->maxSize || i >= rArray->currSize) {
			puts("Invalid remove index");
			return 0;
		}
		else {
			int j;
			int tmp = 0;
			//beginning case, shift left
			if (i == 0) {
				tmp = rArray->array[0];
				for (j = 1; j < (rArray->currSize - 1); j++) {
					rArray->array[j-1] = rArray->array[j];					
				}
				rArray->currSize--;
				rArray->array = realloc(rArray->array, sizeof(int) * rArray->currSize);
				if (rArray->array == NULL) {
					puts("remove failed to realloc memory");
				}
			}
			//middle case
			else if (i > 0 && i < (rArray->currSize - 1)) {
				tmp = rArray->array[0];
				for (j = 0; j < (rArray->currSize - 1); j++) {
					if (j >= i) {
						rArray->array[j] = rArray->array[j+1];
					}
				}
				rArray->currSize--;
				rArray->array = realloc(rArray->array, sizeof(int) * rArray->currSize);
				if (rArray->array == NULL && rArray->currSize > 0) {
					puts("remove failed to realloc memory");
				}
			}
			//end case
			else {
				tmp = rArray->array[rArray->currSize - 1];
				rArray->currSize--;
				rArray->array = realloc(rArray->array, sizeof(int) * rArray->currSize);
			}
			if (rArray->currSize == 0) {
				puts("array is empty, deallocating");
			}
			
			return tmp;
		}
	}
	return 0;
}