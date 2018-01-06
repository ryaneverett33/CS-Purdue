#include "DLList.h"
#include <stdio.h>
#include <stdlib.h>

#define debug 0

DLNode *head;
DLNode *tail;
int items;

struct DLList *list;

//Did not implement this using a Sentinel Node. The handout doesn't say to use a sentinel.
//Screw Sentinels...and cout for that matter.

DLList::DLList()
{
    //Constructor
    head = new struct DLNode;
    tail = new struct DLNode;
    head = NULL;
    tail = NULL;
    items = 0;
}

DLList::~DLList()
{
    //Destructor
    struct DLNode *nextItem = NULL;
    struct DLNode *currItem = head;
    while(currItem != NULL) {
        nextItem = currItem->next;
        delete currItem;
        currItem = nextItem;
    }
    if (nextItem != NULL) delete nextItem;
    if (currItem != NULL) delete currItem;
    items = 0;
    delete head;
    delete tail;
}

void DLList::print()
{
    //Format index:data
    int i = 0;
    struct DLNode *currItem = head;
    while(currItem != NULL) {
        printf("%d\n", currItem->data);
        currItem = currItem->next;
        i++;
    }
}

void DLList::printSorted()
{
    //Ascending order because why not
    int sorted[items];
    //load the list into the array, then sort the array. Lol, efficiency
    struct DLNode *currItem = head;
    int i = 0;
    bool didSwap = false;
    while(currItem != NULL) {
        sorted[i] = currItem->data;
        currItem = currItem->next;
        i++;
    }
    //sort items
    do {
        didSwap = false;
        for (i = 1; i < items; i++) {
            if (sorted[i - 1] > sorted[i])
            {
                didSwap = true;
                //swap positions
                int tmp;
                tmp = sorted[i-1];
                sorted[i-1] = sorted[i];
                sorted[i] = tmp;
            }
        }
    }
    while (didSwap);
    for (i = 0; i < items; i++) {
        printf("%d:%d\n", i, sorted[i]);
    }
}
void DLList::insert(int data) {
	if (head == NULL && tail == NULL) {
		//list is empty, just use insertFront
		return insertFront(data);
	}
	else {
		//list is not empty, add to the end
		DLNode *newNode = new struct DLNode;
		newNode->data = data;
		newNode->next = NULL;
		newNode->prev = tail;
		tail->next = newNode;
		tail = newNode;
		items++;
	}
}
void DLList::insertFront(int data)
{
    //insert as head, modify head to be second object
    struct DLNode *newNode = new struct DLNode;
    if (head == NULL && tail == NULL) {
        if (debug) puts("inserting first object into the list");
        head = newNode;
        tail = newNode;
        newNode->data = data;
        newNode->prev = NULL;
        newNode->next = NULL;
        items++;
        return;
    }
    newNode->data = data;
    newNode->next = head;
    newNode->prev = NULL;
    if  (head == tail) {
        //one item in element, set previous head as tail
        tail = head;
    }
    //previous head is not the only item in the list, don't modify the tail
    head->prev = newNode;
    head = newNode;
    items++;
}
void DLList::remove(int data) {
	if (head == NULL && tail == NULL) {
		if (debug) puts("remove(): list is empty");
		return;
	}
	DLNode *currNode = head;
	bool didRemove = false;
	while (currNode != NULL) {
		if (currNode->data == data) {
			if (currNode == head) {
				//remove first object
				if (head == tail) {
					//list has one object in it, WELL FOR NOW
					removeLast(data);
					didRemove = true;
					return;
				}
				else {
					//list has one more than one object but we're gonna remove the first object
					head->next->prev = NULL;
					head = head->next;
					delete currNode;
					didRemove = true;
					return;
				}
			}
			else if (currNode == tail) {
				//removing last object, if only there was a function for this...
				removeLast(data);
				didRemove = true;
				return;
			}
			else {
				currNode->prev->next = currNode->next;
				currNode->next = currNode->prev;
				delete currNode;
				didRemove = true;
				return;
			}
		}
		else {
			currNode = currNode->next;	
		}
	}
	if (!didRemove) {
		if (debug) puts("remove(): didn't remove, cry sadly");
	}
}

bool DLList::removeLast(int & data)
{
    if (items == 0 || (head == NULL && tail == NULL)) {
        if (debug) puts("removeLast(): List is empty");
        return false;
    }
    //Not sure what's happened
    /*if (data == NULL) {
        if (debug) puts("removeLast(): Data argument is NULL");
    }*/
	if (items == 1) {
        //remove only element
        struct DLNode *currNode = head;
        data = currNode->data;
        delete currNode;
        head = NULL;
        tail = NULL;
        items = 0;
        return true;
    }
    else {
        struct DLNode *currNode = tail;
        tail = currNode->prev;
        data = currNode->data;
        delete currNode;
        tail->next = NULL;
        items--;
        return true;
    }
}

DLList * DLList::difference(DLList & list)
{
	//difference is the set A minus the intesection of set A and B
	DLList *intersect = intersection(list);
	DLList * diff = new DLList();
	DLNode *currNode = head;
	DLNode *currNode2 = intersect->head;
	//loop through elements in list 1, check if element is in list2, if not add it to diff list
	while (currNode != NULL) {
		currNode2 = intersect->head;
		bool doesExist = false;
		while (currNode2 != NULL) {
			if (currNode2->data == currNode->data) {
				doesExist = true;
				break;
			}
			currNode2 = currNode2->next;
		}
		if (!doesExist) {
			diff->insert(currNode->data);
		}
		currNode = currNode->next;
	}
	return diff;
}

DLList * DLList::getRange(int start, int end)
{
    if (end < start) {
        if (debug) puts("Range(): End index is before start index, not happening");
        return NULL;
    }
	int index = 0;
	DLList *newList = new DLList();
	DLNode *currNode = head;
	while(currNode != NULL) {
		if (index >= start && index <= end) {
			newList->insert(currNode->data);
		}
		currNode = currNode->next;
		index++;
	}
	return newList;
}

DLList * DLList::intersection(DLList & list)
{
	/*if (list->head == NULL || list->tail == NULL) {
		if (debug) puts("intersection(): supplied list argument is empty");
		return NULL;
	}*/
	DLList * list3 = new DLList();
	//loop through all elements of current List, check if element exists in list supplied, if it does then check
	//if it's already in list3, if not in list3 then add
	DLNode *currNode = head;	//our list
	DLNode *currNode2 = list.head;	//their list
	DLNode *currNode3 = NULL;
	while (currNode != NULL) {
		currNode2 = list.head;		//reset position
		//check if element exists in supplied list
		while (currNode2 != NULL) {
			if (currNode2->data == currNode->data) {
				//found a match, check if it's already in list3
				currNode3 = list3->head;
				bool doesExist = false;
				while (currNode3 != NULL) {
					if (currNode3->data == currNode2->data) {
						doesExist = true;
						break;
					}
					else {
						currNode3 = currNode3->next;
					}
				}
				if (!doesExist) {
					//value doesn't exist, add it
					list3->insert(currNode2->data);
					break;
				}
			}
			else {
				currNode2 = currNode2->next;
			}
		}
		currNode = currNode->next;
	}
	
	return list3;
}

void DLList::removeRange(int start, int end)
{
	//convert list to array, iterate through array, if index is within bounds, remove data from list
	if (end < start) {
		if (debug) puts("Range(): End index is before start index, not happening");
		return;
	}
	int index = 0;
	int *array = new int[items];
	DLNode *currNode = head;
	while(currNode != NULL) {
		array[index] = currNode->data;
		currNode = currNode->next;
		index++;
	}
	//iterate through array
	for (int i = 0; i < items; i++) {
		if (i >= start && i <= end) {
			remove(array[i]);
		}
	}
}
