#include <stdio.h>
#include <stdlib.h>
#include "io.h"

void printTable(hashtable_t *table) {
	if (table == NULL) {
		puts("printTable(): table is NULL");
	}
	hashtable_ent_t *currObject;
	int i, j;
	printf("table_len: %d\n",(int)table->table_len);
	for (i = 0; i < (table->table_len); i++) {
		if (table->table[i] == NULL) {
			printf("%d: Empty\n", i);
			continue;
		}
		else {
			currObject = table->table[i];
			j = 0;
			while (currObject != NULL) {
				printf("%d-%d: %s %lf\n", i, j, (currObject->key), (currObject->value));
				currObject = currObject -> next;
				j++;
			}
		}
	}
}
void printNode(node_t *node) {
	puts("Printing Node");
	printf("Node Timestamp: %ld\n", node->timestamp);
	printf("Node transaction_type: %d\n", node->transaction_type);
	printf("Node company1: %s\n", node->company1);
	printf("Node company2: %s\n", node->company2);
	printf("Node value: %lf\n", node->value);
}
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

int main() {
	puts("testing io");
	/*FILE *fp;
	
	fp = fopen("accounts_info.txt" , "r");
	
	hashtable_t *table = read_accounts(fp);
	//printTable(table);
	FILE *writeIT;
	//Writes over
	writeIT = fopen("testWrite.txt", "w");
	write_accounts(writeIT, table);*/
	
	FILE *transFP;
	
	transFP = fopen("account_transactions.txt", "r");
	linkedlist_t *list = read_transactions(transFP);
	printList(list);
	return 1;
}