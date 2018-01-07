#include <stdlib.h>
#include <stdio.h>
#include "MyMalloc.h"

int main() {
	fprintf(stderr,"Running Left Size Test\n");
	char** arr = malloc(sizeof(char*) * 5);
	for (int i = 0; i < 5; i++) {
		arr[i] = (char*)malloc(1000);
		arr[i] = arr[i] - sizeof(BoundaryTag);
	}
	for (int i = 0; i < 5; i++) {
		BoundaryTag *tag = (BoundaryTag*)arr[i];
		fprintf(stderr, "Size: %d, Left Object Size: %d\n", getSize(tag), tag->_leftObjectSize);
	}
	print_list();
}