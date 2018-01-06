#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "linkedlist.h"

#define debug 0

linkedlist_t *create_linkedlist() {
	linkedlist_t* list = malloc(sizeof(linkedlist_t));
	list->head = NULL;
	list->tail = NULL;
	return list;
}

int add_node(linkedlist_t *list, node_t *node) {
	if (list == NULL || node == NULL) {
		return -1;
	}
	if (list->head == NULL && list->tail == NULL) {
		//list has just been initalized
		if (debug) printf("add_node(): Initializing list, adding first node\n");
		list->head = node;
		list->tail = node;
		node->next = NULL;
		node->prev = NULL;
		
		return 0;
	}
	else if (list->head != NULL && list->tail == NULL) {
		if (debug) printf("add_node(): Tail on list is Null but head is not!\n");
		if (debug) printf("Invalid add!\n");
		return -1;
	}
	else if (list->head == NULL && list->tail != NULL) {
		if (debug) printf("add_node(): Head on list is Null but tail is not!\n");
		if (debug) printf("Invalid add!\n");
		return -1;
	} 
	else if (list->head != NULL && list->tail != NULL) {
		//valid add
		//ASK about a condition in which node->next || ->prev is not NULL
		if (debug) printf("add_node(): Adding node as tail\n");
		list->tail->next = node;
		node->prev = list->tail;
		node->next = NULL;
		list->tail = node;
		
		return 0;
	}
	else {
		if (debug) printf("add_node(): Invalid condition met.\n");
		return -1;
	}
}

int remove_node(linkedlist_t *list, node_t *node) {
	int failed = -1;
	int succeeded = 0;
	node_t *currNode;
	if (list == NULL || node == NULL) {
		return failed;
	}
	if (list->head == NULL && list->tail == NULL) {
		if (debug) printf("remove_node(): list is empty, cannot remove node!\n");
		return failed;
	}
	else if (list->head == NULL || list->tail == NULL) {
		if (debug) printf("remove_node(): list has either an invalid head or tail. Cannot remove node!\n");
		return failed;
	}
	else {
		currNode = list->head;			//start at head, move forward *insert pun here*
		while(currNode != NULL) {
			if (currNode == node) {
				//found node, continue onto deletion
				if (debug) puts("Found node!");
				if (list->head == currNode) {
					//Removing the head, change list and adjacent node (if any)
					if (currNode->prev != NULL) {
						if (debug) puts("remove_node(): Head node does not have a null prev pointer! Will not remove.");
						return failed;
					}
					else if (currNode->next == NULL) {
						//list is one element only
						list->head = NULL;
						list->tail = NULL;
						currNode->next = NULL;
						currNode->prev = NULL;
						if (debug) puts("remove_node(): Successfully removed head node.");
						return succeeded;
					}
					else {
						//list is multi element
						list->head = currNode->next;
						list->head->prev = NULL;
						currNode->next = NULL;
						currNode->prev = NULL;
						if (debug) puts("remove_node(): Successfully removed head node.");
						return succeeded;
					}
				}
				else if (list->tail == currNode) {
					//A single element list has identical tail and head. Head will execute before reaching here
					//Removing the tail, change the list and previous node
					if (currNode->next != NULL) {
						if (debug) puts("remove_node(): Tail node does not have a null next pointer! Will not remove.");
						return failed;
					}
					else {
						list->tail = currNode->prev;
						list->tail->next = NULL;
						currNode->prev = NULL;
						currNode->next = NULL;
						if (debug) puts("remove_node(): Successfully removed tail node.");
						return succeeded;
					}
				}
				else {
					//Removing a middle node, don't mess with list, just change neighbor nodes
					currNode->prev->next = currNode->next;
					currNode->next->prev = currNode->prev;
					currNode->next = NULL;
					currNode->prev = NULL;
					if (debug) puts("remove_node(): Successfully removed middle node.");
					return succeeded;
				}
			}
			else {
				currNode = currNode->next;
			}
		}
		if (debug) puts("remove_node(): could not find node, failed to remove!");
		return failed;
	}
}

node_t *create_node(long int timestamp, short transaction_type, const char *company1, const char *company2, double value) {
	node_t* node = malloc(sizeof(node_t));
	node->timestamp = timestamp;
	node->transaction_type = transaction_type;
	node->value = value;
	char *com1 = malloc(sizeof(company1));
	char *com2 = malloc(sizeof(company2));
	strcpy(com1, company1);
	strcpy(com2, company2);
	node->company1 = com1;
	node->company2 = com2;	

	return node;
}

void delete_node(node_t *node) {
	if (node == NULL) {
		if (debug) puts("delete_node(): Node is null, cannot delete!");
		return;
	}
	if (node->prev != NULL) free(node->prev);
	if (node->next != NULL) free(node->next);
	//free(node->timestamp);
	//free(node->transaction_type);
	if (node->company1 != NULL) free(node->company1);
	if (node->company2 != NULL) free(node->company2);
	//free(node->value);
	//free(node);
}

void free_linkedlist(linkedlist_t *list) {
	if (list == NULL) {
		if (debug) puts("free_linkedlist(): List is NULL, cannot free");
		return;
	}
	//delete each node, then free list
	node_t *currNode;
	currNode = list->head;
	while(currNode != NULL) {
		/*node_t *nextNode;
		nextNode = currNode->next;
		delete_node(currNode);
		currNode = nextNode;*/
		node_t *tmpNode = currNode;
		delete_node(tmpNode);
		currNode = currNode->next;
	}
	puts("free the rest");
	//free list
	free(list);
}

node_t *find_node(linkedlist_t *list, long int timestamp) {
	if (list == NULL) {
		return NULL;
	}
	node_t *currNode = list->head;
	while (currNode != NULL) {
		if (currNode->timestamp == timestamp) {
			return currNode;
		}
		currNode = currNode->next;
	}
	return NULL;
}