#include <stdio.h>
#include <stdlib.h>
#include "hashtable.h"

void printTable(hashtable_t *table) {
	if (table == NULL) return;
	hashtable_ent_t *currObject;
	int i, j;
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
int test1() {
	
}
int main() {
	hashtable_t *table = create_hashtable(5);
	set(table, "key1", 25.0);
	set(table, "jack", 77);
	set(table, "june", 12);
	set(table, "johnny", 33);
	set(table, "chris", 12);
	printTable(table);
	puts("remove johnny and chris");
	remove_key(table, "johnny");
	remove_key(table, "chris");
	puts("update jack");
	set(table, "jack", 99);
	printTable(table);
	free_hashtable(table);
	return 1;
}