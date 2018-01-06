#include <stdlib.h>
#include <stdio.h>

#include "linkedlist.h"

int main() {
	puts("testing for memory leaks. Must squash");
	puts("***********USE VALGRIND**************");
	
	linkedlist_t *list = create_linkedlist();
	node_t* node1 = create_node(5, 1, "google", "apple", 20.0);
	node_t* node2 = create_node(10, 1, "oracle", "dell", 32.0);
	node_t* node3 = create_node(12, 1, "hp", "sun", 15.0);
	add_node(list, node1);
	add_node(list, node2);
	add_node(list, node3);
	free_linkedlist(list);
	return 1;
}