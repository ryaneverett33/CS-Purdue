#include <stdio.h>
#include <stdlib.h>
#include "DLList.h"

int main() {
    /*DLList *list = new DLList();
    puts("Inserting some values");
    list->insertFront(5);
    list->insertFront(25);
    list->insertFront(69);
    list->insertFront(33);
    puts("printing the list");
    list->print();
    puts("Sort it");
    list->printSorted();
    int data;
    list->removeLast(data);
    list->removeLast(data);
    list->print();
	puts("testing insert");
	list->insert(103);
	list->insert(5612);
	list->print();*/
	DLList *list1 = new DLList();
	list1->insert(5);
	list1->insert(6);
	list1->insert(7);
	list1->insert(8);
	DLList *list2 = new DLList();
	list2->insert(4);
	list2->insert(6);
	list2->insert(8);
	list2->insert(10);
	/*puts("The intersection of list1");
	list1->print();
	puts("and list2");
	list2->print();
	puts("is the list");
	DLList *list3 = list1->intersection(*list2);
	list3->print();*/
	DLList *diff = list1->difference(*list2);
	puts("list1 diff list2");
	diff->print();
	DLList *range = list2->getRange(0,2);
	puts("getRange(0,2) of list2");
	range->print();
	list1->removeRange(0,2);
	puts("removeRange(0,2) of list1");
	list1->print();
	
	//should probably more thoroughly test this
    return 1;
}