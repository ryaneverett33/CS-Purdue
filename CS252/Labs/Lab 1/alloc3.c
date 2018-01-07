#include <stdlib.h>
#include <stdio.h>
#include "MyMalloc.h"

int
main( int argc, char **argv )
{

  //test designed to coalesce from both sides of a block
  int * mem1 = (int *) malloc( 8 );
  *mem1 = 10;

  int * mem2 = (int *) malloc( 8 );
  *mem2 = 11;

  int * mem3 = (int *) malloc( 8 );
  *mem3 = 12;

  exit(0);
}
