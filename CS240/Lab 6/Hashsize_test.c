#include <stdio.h>
#include <stdlib.h>
#include "hashtable.h"

int main() {
	hashtable_t *table = create_hashtable(5);
	set(table, "key1", 25.0);
	set(table, "jack", 77);
	set(table, "june", 12);
	free_hashtable(table);
	return 2;
}