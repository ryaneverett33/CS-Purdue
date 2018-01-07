#include <stdio.h>
#include <stdlib.h>
#include "MyMalloc.h"

int main() {
	printf("Before any allocation\m");
	print_list();
	
	int *mem1 = (int*)malloc(8);
	*mem1 = 13;
	
	printf("after allocation\n");
	print_list();
	
	printf("Value: %d\n", *mem1);
	
	return 0;
}
