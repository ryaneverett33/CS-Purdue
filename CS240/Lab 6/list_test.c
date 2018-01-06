/*
**	Linked List Test file
**
*/

#include <stdlib.h>
#include <stdio.h>

#include "linkedlist.h"

#define pass 1
#define fail 0

char * error_messages[3] = {
	"failed basic create","failed basic remove","failed delete all", "failed find node"
};

//Simply prints the info of a node
void printNode(node_t *node) {
	puts("Printing Node");
	printf("Node Timestamp: %ld\n", node->timestamp);
	printf("Node transaction_type: %d\n", node->transaction_type);
	printf("Node company1: %s\n", node->company1);
	printf("Node company2: %s\n", node->company2);
	printf("Node value: %lf\n", node->value);
}
//surprise, it prints the info of a list
void printList(linkedlist_t *list) {
	printf("size of list created: %d\n", (int)sizeof(list));
	int isHeadNULL = 0, isTailNULL = 0;
	node_t* currNode;
	if (list->head == NULL) isHeadNULL = 1;
	if (list->tail == NULL) isTailNULL = 1;
	printf("Is head null?: %d, Is tail null?: %d\n", isHeadNULL, isTailNULL);
	currNode = list->head;
	while(currNode != NULL) {
		printNode(currNode);
		currNode = currNode->next;
	}
}
int test1() {
	puts("testing basic create");
	linkedlist_t *list = create_linkedlist();
	if (list == NULL) return fail;
	node_t* node1 = create_node(5, 1, "google", "apple", 20.0);
	add_node(list, node1);
	if (node1 == NULL) return fail;
	node_t* node2 = create_node(10, 1, "oracle", "dell", 32.0);
	add_node(list, node2);
	if (node2 == NULL) return fail;
	node_t* node3 = create_node(12, 1, "hp", "sun", 15.0);
	add_node(list, node3);
	if (node3 == NULL) return fail;
	printList(list);
	return pass;
}
int test2() {
	puts("testing basic remove");
	linkedlist_t *list = create_linkedlist();
	if (list == NULL) return fail;
	node_t* node1 = create_node(5, 1, "google", "apple", 20.0);
	add_node(list, node1);
	node_t* node2 = create_node(10, 1, "oracle", "dell", 32.0);
	add_node(list, node2);
	node_t* node3 = create_node(12, 1, "hp", "sun", 15.0);
	add_node(list, node3);
	if (remove_node(list, node3) != 0) return fail;
	node_t* node4 = create_node(77, 1, "dell", "google", 69);
	add_node(list, node4);
	if (remove_node(list, node1) != 0) return fail;
	printList(list);
	return pass;
}
int test3() {
	puts("test delete all");
	linkedlist_t *list = create_linkedlist();
	if (list == NULL) return fail;
	node_t* node1 = create_node(5, 1, "google", "apple", 20.0);
	node_t* node2 = create_node(10, 1, "oracle", "dell", 32.0);
	node_t* node3 = create_node(12, 1, "hp", "sun", 15.0);
	add_node(list, node1);
	add_node(list, node2);
	add_node(list, node3);
	if (remove_node(list, node1) != 0) return fail;
	if (remove_node(list, node2) != 0) return fail;
	if (remove_node(list, node3) != 0) return fail;
	printList(list);
	return pass;
}
int test4() {
	puts("test find node");
	linkedlist_t *list = create_linkedlist();
	if (list == NULL) return fail;
	node_t* node1 = create_node(5, 1, "google", "apple", 20.0);
	node_t* node2 = create_node(10, 1, "oracle", "dell", 32.0);
	node_t* node3 = create_node(12, 1, "hp", "sun", 15.0);
	add_node(list, node1);
	add_node(list, node2);
	add_node(list, node3);
	if(find_node(list, 10) != node2) return fail;
	if(find_node(list, 12) != node3) return fail;
	if(find_node(list, 69) != NULL) return fail;
	return pass;
}
void printFail(int test) {
	puts("********************************");
	puts(error_messages[test - 1]);
	puts("********************************");
}
void printPass() {
	puts("*************PASS***************");
}
int main() {
	if (test1() == fail) printFail(1);
	else printPass();
	if (test2() == fail) printFail(2);
	else printPass();
	if (test3() == fail) printFail(3);
	else printPass();
	if (test3() == fail) printFail(3);
	else printPass();
	return 1;
}
