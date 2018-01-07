#include <stdio.h>
#include <stdlib.h>
#include "MyMalloc.h"

int main() {
	//printf("Before any allocation\m");
	//print_list();
	
	int *mem1 = (int*)malloc(8);
	*mem1 = -1;
	free(mem1);

	fprintf(stderr, "After free\n");
	print_list();
	
	return 0;
}
