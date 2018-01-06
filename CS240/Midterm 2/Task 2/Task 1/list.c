#include <stdio.h>
#include <stdlib.h>
#include "list.h"

// Create a newly allocated empty linkedlist_t with head and tail initialized to NULL
DLList *create_linkedlist() {
	DLList *newList = malloc(sizeof(DLList));
	newList->head = NULL;
	newList->tail = NULL;
	return newList;
}

// Create a new ListNode and assign the value of the node to the parameter value. Add the
// node at the tail of the list
void llist_add(DLList * list, int value) {
	if (list == NULL) {
		puts("llist_add(): supplied list is NULL!");
		return;
	}
	DLLItem *node = malloc(sizeof(DLLItem));
	if (node == NULL) {
		puts("llist_add(): Failed to allocate node. Cannot add node");
		return;
	}
	node->value = value;
	if (list->head != NULL && list->tail != NULL) {
		//list has elements, add at end
		node->prev = list->tail;
		node->next = NULL;
		node->prev->next = node;
		list->tail = node;
	}
	else {
		//empty list, create first element
		list->head = node;
		list->tail = node;
	}
}

// Remove the entry with that value in the list.
void llist_remove(DLList * list, int value) {
	if (list == NULL) {
		puts("llist_remove(): supplied list is NULL!");
		return;
	}
	DLLItem *currItem = list->head;
	int i = 0, didFind = 0;
	while (currItem != NULL) {
		if (currItem->value == value) {
			//found item, remove it
			if (i == 0) {
				//printf("Found value at i = %d\n", i);
				list->head->prev = NULL;
				list->head = currItem->next;		
				currItem = NULL;
				didFind = 1;
				break;
			}
			else {
				//printf("Found value at i = %d\n", i);
				if (currItem->next == NULL) {
					//end of list
					list->tail = currItem->prev;
					list->tail->next = NULL;
				}
				else {
					currItem->prev->next = currItem->next;
					currItem->next->prev = currItem->prev;
				}
				didFind = 1;
				currItem = NULL;
				break;
			}
		}
		else {
			//did not find node, continue on
			currItem = currItem->next;
			i++;
		}
	}
	if (!didFind) {
		puts("llist_remove(): Did not find value, cannot remove.");
	}
}

void printList(DLList * list) {
	DLLItem *currItem = list->head;
	int i = 0;
	while (currItem != NULL) {
		printf("%d: %d\n", i, currItem->value);
		currItem = currItem->next;
		i++;
	}
}
void printListInfo(DLList * list) {
	if (list == NULL) return;
	printf("Head value: %d, Tail value: %d\n", list->head->value, list->tail->value);
}