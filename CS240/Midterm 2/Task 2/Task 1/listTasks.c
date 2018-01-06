#include <stdlib.h>
#include <stdio.h>
#include "list.h"

#define fuckyou -1

//Group 1
int llist_insertAfter_ith(DLList * list, int ith, int value) {
	if (list == NULL) {
		return 0;
	}
	DLLItem *currItem = list->head;
	int i = 0;
	while (currItem != NULL) {
		if (i == (ith - 1)) {
			DLLItem *node = malloc(sizeof(DLLItem));
			node->value = value;
			if (currItem->prev == NULL) {
				//at the beginning
				if (list->tail == list->head) {
					//one element list
					list->tail = node;
					list->head->next = node;
					node->prev = list->head;
					node->next = NULL;
					return 1;
				}
				else {
					node->next = currItem->next;
					currItem->next = node;
					node->prev = currItem;
					return 1;
				}
			}
			else if (currItem->next == NULL) {
				// at the end
				list->tail = node;
				currItem->next = node;
				node->prev = currItem;
				node->next = NULL;
				return 1;
			}
			else {
				//somewhere in the middle
				node->next = currItem->next;
				currItem->next = node;
				node->prev = currItem;
				return 1;
			}
		}
		else {
			currItem = currItem->next;
			i++;
		}
	}
	return 0;
}
int llist_remove_ith(DLList * list, int ith) {
	if (list == NULL) {
		return 0;
	}
	int i = 0;
	DLLItem *currItem = list->head;
	while (currItem != NULL) {
		if (i == (ith-1)) {
			puts("found, removing");
			llist_remove(list, currItem->value);
			return 1;
			break;
		}
		else {
			i++;
			currItem = currItem->next;
		}
	}
	return 0;
}
int llist_remove_first(DLList * list) {
	if (list == NULL || list->head == NULL) {
		return 0;
	}
	else {
		llist_remove(list, list->head->value);
		return 1;
	}
}
int llist_remove_last(DLList * list) {
	if (list == NULL || list->tail == NULL) {
		return 0;
	}
	else {
		llist_remove(list, list->tail->value);
		return 1;
	}
}
void llist_insert_first(DLList * list, int value) {
	if (list == NULL) {
		return;
	}
	if (list->head == NULL && list->tail == NULL) {
		//list is empty, create first element
		DLLItem *node = malloc(sizeof(DLLItem));
		node->value = value;
		list->head = node;
		list->tail = node;
		node->prev = NULL;
		node->next = NULL;
		return;
	}
	else {
		//list isn't empty
		DLLItem *node = malloc(sizeof(DLLItem));
		node->value = value;
		node->prev = NULL;
		node->next = list->head;
		list->head->prev = node;
		list->head = node;
		return;
	}
}
void llist_insert_last(DLList * list, int value) {
	if (list == NULL) {
		return;
	}
	if (list->head == NULL && list->tail == NULL) {
		//list is empty, create first element
		DLLItem *node = malloc(sizeof(DLLItem));
		node->value = value;
		node->prev = NULL;
		node->next = NULL;
		list->head = node;
		list->tail = node;
		return;
	}
	else {
		//list isn't empty, continue normally
		DLLItem *node = malloc(sizeof(DLLItem));
		node->value = value;
		node->prev = list->tail;
		node->next = NULL;
		list->tail->next = node;
		list->tail = node;
		return;
	}
}

//Group 2
DLList *llist_intersection(DLList * list1, DLList * list2) {
	//loop through each element in list1, compare to each element in list2, if equal then
	//check if in list3, if not in list3 then add to list3
	if (list1 == NULL || list2 == NULL) {
		return NULL;
	}
	if (list1->head == NULL || list2->head == NULL) {
		puts("Invalid lists, return null");
		return NULL;
	}
	DLList *list3 = create_linkedlist();
	DLLItem *currItem_1 = list1->head;
	DLLItem *currItem_2 = list2->head;
	DLLItem *currItem_3;
	while(currItem_1 != NULL) {
		while(currItem_2 != NULL) {
			if (currItem_1->value == currItem_2->value) {
				//check if already in list3
				currItem_3 = list3->head;
				int inList = 0;
				while(currItem_3 != NULL) {
					if (currItem_3->value == currItem_1->value) {
						inList = 1;
						break;
					}
					else {
						currItem_3 = currItem_3->next;
					}
				}
				if (!inList) {
					llist_add(list3, currItem_1->value);
				}
				break;
			}
			else {
				currItem_2 = currItem_2->next;
			}
		}
		currItem_2 = list2->head;
		currItem_1 = currItem_1->next;
	}
	return list3;
}
DLList *llist_union(DLList * list1, DLList * list2) {
	//add each element of list1 to list3, loop through list2, if in list2 and not in list3 then
	//add to list3
	if (list1 == NULL || list2 == NULL) {
		return NULL;
	}
	if (list1->head == NULL && list2->head == NULL) {
		puts("both lists are empty");
		return NULL;
	}
	DLList *list3 = create_linkedlist();
	DLLItem *currItem_1 = list1->head;
	DLLItem *currItem_2 = list2->head;
	DLLItem *currItem_3 = list3->head;
	//add list1 to list3
	while(currItem_1 != NULL) {
		currItem_3 = list3->head;
		int inList = 0;
		while (currItem_3 != NULL) {
			if (currItem_3->value == currItem_1->value) {
				inList = 1;
				break;
			}
			else {
				currItem_3 = currItem_3->next;
			}
		}
		if (!inList) llist_add(list3,currItem_1->value);
		currItem_1 = currItem_1->next;
	}
	while(currItem_2 != NULL) {
		int inList = 0;
		while(currItem_3 != NULL) {
			if (currItem_3->value == currItem_2->value) {
				inList = 1;
				break;
			}
			else {
				currItem_3 = currItem_3->next;
			}
		}
		if (!inList) {
			llist_add(list3, currItem_2->value);
		}
		currItem_3 = list3->head;
		currItem_2 = currItem_2->next;
	}
	return list3;
}
//swap nodes
void nodeSwap(DLList *list, DLLItem *node1, DLLItem *node2) {
	//node 1 switches places with node2
	if (list->head == node1) {
		
	}
	else if (list->head == node2) {
		
	}
	if (list->tail == node1) {
		
	}
	else if (list->tail == node2) {
		
	}
	
}
void llist_sort(DLList * list, int ascending) {
	if (list == NULL || list->head == NULL) {
		return;
	}
	int didSwap = 0;
	DLLItem *currItem = list->head;
	if (ascending) {
		do {
			didSwap = 0;
			currItem = list->head;
			while(currItem != NULL) {
				if ()
			}
		}
		while (didSwap);
	}
	else {
		do {
			didSwap = 0;
			currItem = list->head;
			while(currItem != NULL) {
				
			}
		}
		while (didSwap);
	}
}
void llist_removeRange(DLList * list, int low, int high) {
	if (list == NULL || list->head == NULL) {
		return;
	}
	DLLItem *currItem = list->head;
	while(currItem != NULL) {
		if (currItem->value >= low && currItem->value <= high) {
			llist_remove(list,currItem->value);
		}
		currItem = currItem->next;
	}
}