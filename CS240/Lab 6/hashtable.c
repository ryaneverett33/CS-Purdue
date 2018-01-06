#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "hashtable.h"

#define debug 0

hashtable_t *create_hashtable(int max_size) {
	hashtable_t *hashtable = malloc(sizeof(hashtable_t));
	hashtable->table = malloc(sizeof(hashtable_ent_t) * max_size);
	int i = 0;
	for (i = 0; i < max_size; i++) {
		hashtable->table[i] = NULL;
	}
	hashtable->table_len = max_size;
	return hashtable;
}

void free_hashtable(hashtable_t *table) {
	if (table == NULL) {
		if (debug) puts("free_hashtable(): table argument is NULL");
		return;
	}
	//free table array
	int i;
	for (i = 0; i < table->table_len; i++) {
		if (table->table[i] != NULL) {
			//loop through and free items
			hashtable_ent_t *nextItem = NULL;
			hashtable_ent_t *currItem = table->table[i];
			while (currItem != NULL) {
				nextItem = currItem->next;
				remove_key(table, currItem->key);
				currItem->next = 0;
				currItem = nextItem;
			}
			if (debug) printf("sizeof table entry: %d\n", (int)sizeof(table->table[i]));
		}
	}
	//might cause problems
	//free (table->table);
	if (debug) printf("sizeof table array: %d\n", (int)sizeof(table->table));
	if (debug) printf("sizeof reference int: %d\n", (int)sizeof(int));
	table->table = NULL;
	
	//free table variable
	//free(table);
}

int get(hashtable_t *table, const char *key, double *value) {
	int pass = 0, fail = -1, index;
	if (table == NULL) {
		if (debug) puts("get(): table argument is NULL");
		return fail;
	}
	if (key == NULL) {
		if (debug) puts("get(): key argument is NULL");
		return fail;
	}
	index = hash(key) % (table->table_len);
	if (!key_exists(table, key)) {
		if (debug) puts("get(): key does not exist");
		return fail;
	}
	else {
		if (debug) puts("get(): key exists");
		// find that key
		hashtable_ent_t *currObject = table->table[index];
		while (currObject != NULL) {
			if (strcmp(currObject->key, key) == 0) {
				//found key
				*value = currObject->value;
				return pass;
			}
			currObject = currObject->next;
		}
	}
	return fail;
}

int set(hashtable_t *table, const char *key, double value) {
	//index is temporary holder for the placement location
	int pass = 0, fail = -1, index;
	if (table == NULL) {
		if (debug) puts("set(): table argument is NULL");
		return fail;
	}
	if (key == NULL) {
		if (debug) puts("set(): key argument is NULL");
		return fail;
	}
	hashtable_ent_t *object = malloc(sizeof(hashtable_ent_t));
	if (object == NULL) {
		if (debug) puts("set(): object failed to allocate");
		return fail;
	}
	//check if key exists already
	index = hash(key) % (table->table_len);
	if (key_exists(table, key)) {
		if (debug) puts("set(): key already exists");
		hashtable_ent_t *currObject = table->table[index];
		if (debug && currObject == NULL) puts("currObject is null before starting check");
		while(currObject != NULL) {
			if (debug) printf("currStr: %s, key: %s\n", currObject->key, key);
			if (strcmp(key, currObject->key) == 0) {
				if (debug) puts("set(): updating key");
				currObject->value = currObject->value + value;
				
				free(object);
				return pass;
			}
			currObject = currObject->next;
		}
		if (debug) puts("set(): failed to find object, returning fail");
		return fail;
	}
	object->key = strcpy(malloc(sizeof(key)),key);
	object->value = value;
	if (debug) printf("Indexing at index %d\n", index);
	if (table->table[index] != NULL) {
		if (debug) puts("Index is not empty, adding onto list");
		//do add on to list
		hashtable_ent_t *currObject = table->table[index];
		while(currObject->next != NULL) {
			currObject = currObject->next;
		}
		//we are at the last object, add on to it
		if (debug) printf("adding key: %s, value: %lf\n", (object->key),(object->value));
		currObject->next = object;
		object->next = NULL;
	}
	else {
		if (debug) puts("Index is empty, creating list");
		table->table[index] = object;
		object->next = NULL;
	}
	return pass;
}

int key_exists(hashtable_t *table, const char *key) {
	//index is temporary holder for the placement location
	int exists = 1, notexist = 0, nullparam = -1, index;
	if (table == NULL) {
		if (debug) puts("key_exists(): table argument is NULL");
		return nullparam;
	}
	if (key == NULL) {
		if (debug) puts("key_exists(): key argument is NULL");
		return nullparam;
	}
	//find where it should be, look there
	index = hash(key) % (table->table_len);
	if (table->table[index] == NULL) {
		if (debug) puts("key_exists(): table is empty at index");
		return notexist;
	}
	else {
		//search at index to find key
		hashtable_ent_t *currObject = table->table[index];
		while(currObject != NULL) {
			if (strcmp(key, currObject->key) == 0) {
				if (debug) puts("key_exists(): key exists!");
				return exists;
			}
			currObject = currObject->next;
		}
	}
	if (debug) puts("key_exists(): key does not exist");
	return notexist;
}

int remove_key(hashtable_t *table, const char *key) {
	int fail = -1, pass = 0, index;
	hashtable_ent_t *currObject = NULL;
	hashtable_ent_t *prevObject = NULL;
	if (table == NULL) {
		if (debug) puts("remove_key(): table argument is NULL");
		return fail;
	}
	if (key == NULL) {
		if (debug) puts("remove_key(): key argument is NULL");
		return fail;
	}
	if (key_exists(table, key)) {
		if (debug) puts("remove_key(): key exists, finding it");
		index = hash(key) % (table->table_len);
		currObject = table->table[index];
		while(currObject != NULL) {
			if (strcmp(key, currObject->key) == 0) {
				if (debug) puts("remove_key(): found key, removing");
				if (prevObject == NULL) {
					//beginning of list
					table->table[index] = currObject->next;
					free(currObject->key);	//key is copied, so delete the copy
					free(currObject);
					return pass;
				}
				else {
					//somewhere in the middle/end
					prevObject->next = currObject->next;
					free(currObject->key);	//see above
					free(currObject);
					return pass;
				}
			}
			currObject = currObject->next;
			prevObject = currObject;
		}
	}
	else {
		return fail;
	}
	if (debug) puts("remove_key(): should not have reached here, return fail");
	return fail;
}