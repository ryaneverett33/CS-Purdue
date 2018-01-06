#include <stdlib.h>
#include <stdio.h>
#include "list.h"

void testAux() {
	puts("Testing Auxilary Functions");
	DLList *list = create_linkedlist();
	llist_add(list, 5);
	llist_add(list, 7);
	llist_add(list, 9);
	llist_add(list, 11);
	printListInfo(list);
	printList(list);
	puts("removing it all");
	llist_remove(list, 5);
	llist_remove(list, 7);
	llist_remove(list, 9);
	llist_remove(list, 11);
	printList(list);
	puts("Test remove at end");
	DLList *list2 = create_linkedlist();
	llist_add(list2, 5);
	llist_add(list2, 7);
	llist_add(list2, 9);
	llist_remove(list2, 9);
	printList(list2);
	llist_add(list2, 11);
	printList(list2);
}
void task211() {
	puts("Testing Task 21-1");
	DLList *list = create_linkedlist();
	llist_add(list, 5);
	llist_add(list, 7);
	llist_add(list, 9);
	llist_add(list, 11);
	puts("Add 25 after 2nd");
	if(!llist_insertAfter_ith(list, 2,25)) {
		puts("Insert Middle failed");
	}
	printList(list);
	puts("Add 69 after 5nd");
	if(!llist_insertAfter_ith(list,5,69)) {
		puts("Insert End failed");
	}
	printList(list);
	DLList *list2 = create_linkedlist();
	llist_add(list2, 7);
	puts("Add 33 after 1nd");
	if(!llist_insertAfter_ith(list2,1,33)) {
		puts("Insert Only Element Failed");
	}
	printList(list2);
	if(llist_insertAfter_ith(create_linkedlist(),5,1)) {
		puts("Insert Element in Empty List Failed");
	}
}
void task212() {
	puts("Testing Task 21-2");
	DLList *list = create_linkedlist();
	puts("adding shit");
	llist_add(list, 5);
	llist_add(list, 7);
	llist_add(list, 9);
	llist_add(list, 11);
	//remove 1 and 3 spot
	puts("remove 1st");
	llist_remove_ith(list, 1);
	printList(list);
	puts("remove 3rd");
	llist_remove_ith(list, 3);
	puts("print");
	printList(list);
}
void task213() {
	puts("Testing Task 21-3");
	DLList *list = create_linkedlist();
	puts("adding shit");
	llist_add(list, 5);
	llist_add(list, 7);
	if(!llist_remove_first(list)) {
		puts("Two nodes. Test failed");
	}
	printList(list);
	DLList *list2 = create_linkedlist();
	puts("adding shit");
	llist_add(list2, 5);
	printList(list2);
	if (!llist_remove_first(list2)) {
		puts("One node. Test failed");
	}
	if (llist_remove_first(create_linkedlist())) {
		puts("Empty list. Test failed.");
	}
}
void task214() {
	puts("Testing Task 21-4");
	DLList *list = create_linkedlist();
	puts("adding shit");
	llist_add(list, 5);
	llist_add(list, 7);
	if(!llist_remove_last(list)) {
		puts("Two nodes. Test failed");
	}
	printList(list);
	DLList *list2 = create_linkedlist();
	puts("adding shit");
	llist_add(list2, 5);
	if (!llist_remove_last(list2)) {
		puts("One node. Test failed");
	}
	printList(list2);
	if (llist_remove_last(create_linkedlist())) {
		puts("Empty list. Test failed.");
	}
}
void task215() {
	puts("Testing Task 21-5");
	DLList *list = create_linkedlist();
	llist_add(list, 5);
	llist_add(list, 7);
	llist_add(list, 9);
	llist_add(list, 11);
	puts("Add 25 at the front");
	llist_insert_first(list,25);
	printList(list);
	DLList *list2 = create_linkedlist();
	llist_add(list2, 5);
	puts("Add 33 at the front");
	llist_insert_first(list2,33);
	printList(list2);
	puts("Add 69 to empty list");
	DLList *list3 = create_linkedlist();
	llist_insert_first(list3,69);
	printList(list3);
}
void task216() {
	puts("Testing Task 21-6");
	DLList *list = create_linkedlist();
	llist_add(list, 5);
	llist_add(list, 7);
	llist_add(list, 9);
	llist_add(list, 11);
	puts("Add 25 at the end");
	llist_insert_last(list,25);
	printList(list);
	DLList *list2 = create_linkedlist();
	llist_add(list2, 5);
	puts("Add 33 at the end");
	llist_insert_last(list2,33);
	printList(list2);
	puts("Add 69 to empty list");
	DLList *list3 = create_linkedlist();
	llist_insert_last(list3,69);
	printList(list3);
}
void task221() {
	DLList *list1 = create_linkedlist();
	DLList *list2 = create_linkedlist();
	llist_add(list1,1);
	llist_add(list1,2);
	llist_add(list1,3);
	llist_add(list1,4);
	llist_add(list1,5);
	llist_add(list2,2);
	llist_add(list2,4);
	llist_add(list2,6);
	DLList *list3 = llist_intersection(list1,list2);
	printList(list3);
	//should print 2,4
	list1 = create_linkedlist();
	list2 = create_linkedlist();
	llist_add(list1,2);
	llist_add(list1,4);
	llist_add(list1,6);
	llist_add(list2,1);
	llist_add(list2,3);
	llist_add(list2,5);
	list3 = llist_intersection(list1,list2);
	puts("should print empty list");
	printList(list3);
	list1 = create_linkedlist();
	list2 = create_linkedlist();
	list3 = llist_intersection(list1,list2);
	puts("Should print blank list info");
	printListInfo(list3);
}
void task222() {
	DLList *list1 = create_linkedlist();
	DLList *list2 = create_linkedlist();
	llist_add(list1,1);
	llist_add(list1,2);
	llist_add(list1,3);
	llist_add(list2,4);
	llist_add(list2,5);
	llist_add(list2,6);
	DLList *list3 = llist_union(list1,list2);
	printList(list3);
	puts("");
	//should print 1,2,3,4,5,6
	list1 = create_linkedlist();
	llist_add(list1,1);
	llist_add(list1,2);
	list3 = llist_union(list1,list1);
	printList(list3);
	puts("");
	//should print 1,2
	list1 = create_linkedlist();
	list2 = create_linkedlist();
	llist_add(list1,0);
	llist_add(list1,0);
	llist_add(list1,0);
	llist_add(list2,1);
	llist_add(list2,2);
	list3 = llist_union(list1,list2);
	printList(list3);
	//should print 0,1,2
	puts("");
}
void task224() {
	DLList *list1 = create_linkedlist();
	llist_add(list1,1);
	llist_add(list1,2);
	llist_add(list1,3);
	llist_add(list1,4);
	llist_add(list1,5);
	llist_add(list1,6);
	llist_removeRange(list1,2,4);
	//should print 1,5,6
	printList(list1);
	puts("");
	list1 = create_linkedlist();
	int i;
	for (i = 0; i < 20; i++) {
		llist_add(list1,i);
	}
	llist_removeRange(list1,1,12);
	//should print 0,13,14,15,16,17,18,19
	printList(list1);
}

int main() {
	//testAux();
	//task212();
	//task213();
	//task214();
	//task211();
	//task215();
	//task216();
	//task221();
	//task222();
	task224();
	return 1;
}