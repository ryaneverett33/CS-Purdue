#include <stdlib.h>
#include <stdio.h>
#include "MyMalloc.h"

int allocations = 5;

int main() {
  printf("\n---- Running test2 ---\n");
  
  // test performs a few large allocations, beyond 2MB.
  // this means more chunks must be requested from the OS.
  int i;
  for ( i = 0; i < allocations; i++ ) {
    char * p1 = (char *) malloc(1500000);
    *p1 = 100;
    print_list();
  }
  //reverse_list();
  exit( 0 );
}
/*void reverse_list() {
  fprintf(stderr, "\nREVERSE\n");
  fprintf(stderr, "FreeList: ");
    FreeObject *ptr = _freeList->free_list_node._prev;
    while (ptr != _freeList) {
        long offset = (long)ptr - (long)_memStart;
        fprintf(stderr, "[offset:%ld,size:%zd]", offset, getSize(&ptr->boundary_tag));
        ptr = ptr->free_list_node._prev;
        if (ptr != NULL)
            fprintf(stderr, "->");
    }
    fprintf(stderr, "\n");
}*/