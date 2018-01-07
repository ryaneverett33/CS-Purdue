#define DEBUG 0
#include <stdlib.h>
#include <stdio.h>
#include "MyMalloc.h"

int allocations = 65535;

int main() {
  printf("\n---- Running test1 ---\n");
  if (DEBUG) print_list();
  //test performs many small allocations, up to 2MB
  int i;
  for ( i = 0; i < allocations; i++ ) {
	if (i == 65501) {
		int debug = 5;
	}
	//fprintf(stderr, "i: %d of %d\n", i, allocations);
    char * p1 = (char *) malloc(15 );
    *p1 = 100;
	
 	//print_list();
  }
  //fprintf(stderr, "Allocated all objects\n");
  print_list();
  exit( 0 );
}

