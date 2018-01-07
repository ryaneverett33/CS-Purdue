#include <stdlib.h>
#include <stdio.h>
#include "MyMalloc.h"

int
main( int argc, char **argv )
{

  //test designed to coalesce from both sides of a block
  int * mem1 = (int *) malloc( 8 );
  *mem1 = 10;
  
  fprintf(stderr, "mem1 tag at: %p\n", (void*)(char*)mem1 - sizeof(BoundaryTag));
  free(mem1);

  int * mem2 = (int *) malloc( 8 );
  *mem2 = 11;
  
  fprintf(stderr, "mem2 tag at: %p\n", (void*)(char*)mem2 - sizeof(BoundaryTag));
  free(mem2);
  
  int * mem3 = (int *) malloc( 8 );
  *mem3 = 12;

  fprintf(stderr, "mem3 tag at: %p\n", (void*)(char*)mem3 - sizeof(BoundaryTag));
  free(mem3);
  
  exit(0);
}
