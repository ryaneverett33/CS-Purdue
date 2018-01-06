#include "ArrayList.h"
#include <stdio.h>

void printList (ArrayList<int> *list) {
	printf("Printing list of size:%d\n", list->size());
	for (int i = 0; i < list->size(); i++) {
		int item = list->get(i);
		printf("%d : %d\n", i, item);
	}
}
void testOperators() {
	ArrayList<int> *list = new ArrayList<int>();
	ArrayList<int> *list2 = new ArrayList<int>();
	ArrayList<int> *list3 = new ArrayList<int>();
	ArrayList<int> *list4 = new ArrayList<int>();
	ArrayList<int> *list5 = new ArrayList<int>();
	
	puts("Test 1");
	list->add(5);
	list->add(7);
	list2->add(6);
	list2->add(8);
	*list<<*list2;
	*list+=*list2;
	*list+=9;
	list->sort();
	printList(list);
	
	puts("Test 2");
	*list3<<5;
	*list3<<7;
	*list3<<9;
	printList(list3);
	
	puts("Equivalence tests");
	if (*list3 == *list) {
		puts("failed first test");
	}
	if (!(*list3 == *list3)) {
		puts("failed self equivalence test");
	}
	list4->add(1);
	list4->add(2);
	list5->add(1);
	list5->add(2);
	if (!(*list4 == *list5)) {
		puts("failed unique equivalence test");
	}
}
void testCopyConstructor() {
	ArrayList<int> *list1 = new ArrayList<int>();
	list1->add(5);
	list1->add(7);
	list1->add(10);
	ArrayList<int> *list2(list1);
	if (!(*list1 == *list2)) {
		puts("CopyConstructor failed equivalency test");
	}
	else {
		puts("Passed equivalency test");
	}
	puts("Test assignment operator");
	ArrayList<int> *list3 = list1;
	if (!(*list1 == *list3)) {
		puts("Assignment operator failed equivalency test");
	}
	else {
		puts("Passed equivalency test");
	}
}
int main() {
	/*ArrayList<int> *list = new ArrayList<int>();
	list->add(5);
	list->add(7);
	printList(list);
	puts("pushing 0 to the front");
	list->push_front(1);
	printList(list);
	puts("pushing 33 to the front");
	list->push_front(33);
	printList(list);
	puts("pushing -5 and -7 to the back");
	list->push_back(-5);
	list->push_back(-7);
	printList(list);*/
	/*puts("stupid add");
	try {
		list->add(15,10);
	}
	catch (std::exception e) {
		puts("add failed as expected");
	}*/
	/*puts("add after stupid add: 99");
	list->add(99);
	printList(list);
	puts("remove all the things!");
	list->remove((const int)7,NULL);
	list->remove(0);
	bool *ok = new bool;
	list->remove((const int)99,ok);
	if (*ok != true) {
		puts("remove(const,*bool) failed to set pointer");
	}
	printList(list);*/
	testOperators();
	testCopyConstructor();
}