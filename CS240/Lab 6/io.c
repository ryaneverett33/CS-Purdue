#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "io.h"
#include "hashtable.h"
#include "linkedlist.h"

#define debug 0
#define charBufferSize 128
#define transactionBufferSize 32

//Transaction types
//ADD : 0
//REMOVE : 1
//TRANSFER : 2
//NULL : -1

hashtable_t *read_accounts(FILE *fd) {
	//
	// !!TODO!!
	// Validate file before reading it
	//
	if (fd == NULL) {
		if (debug) puts("read_accounts(): File argument is NULL");
		return NULL;
	}
	char str[512];						//tmp string to write file line to
	hashtable_t *table = create_hashtable(32);
	if (debug) puts("begin reading accounts");
	while(fgets(str,512,fd) != NULL) {
		//handle creating hashtable
		char *company = malloc(sizeof(char) * charBufferSize) ;
		double *value = malloc(sizeof(double));
		if(sscanf(str,"%s %lf",company, value) == EOF) { if (debug) puts("sscanf::read_accounts() encountered an EOF"); }
		if (company == NULL) { if (debug) puts("read_accounts(): sscanf produced NULL company"); }
		if (value == NULL) { if (debug) puts("read_accounts(): sscanf produced NULL value"); }
		if (company != NULL && value != NULL) {
			if (set(table, company, *value) == -1) {
				if (debug) puts("read_accounts(): could not add company. set returned -1");
			}
			else {
				if (debug) printf("added: %s,%lf\n", company, *value);
				free(company);
				free(value);
			}
		}
	}
	return table;
}

void write_accounts(FILE *fd, hashtable_t *accounts) {
	if (fd == NULL) {
		if (debug) puts("write_accounts(): File argument is NULL");
		return;
	}
	if (accounts == NULL) {
		if (debug) puts("write_accounts(): Accounts argument is NULL");
		return;
	}
	
	//Ha, I wrote a writeTable function already. Copy and pastteee
	hashtable_ent_t *currObject;
	int i, j;
	for (i = 0; i < (accounts->table_len); i++) {
		if (accounts->table[i] == NULL) {
			//if (debug) printf("%d: Empty\n", i);
			continue;
		}
		else {
			currObject = accounts->table[i];
			j = 0;
			while (currObject != NULL) {
				//fprintf(fd, "%d-%d: %s %lf\n", i, j, (currObject->key), (currObject->value));
				fprintf(fd, "%s %lf\n", (currObject->key), (currObject->value));
				currObject = currObject -> next;
				j++;
			}
		}
	}
}

linkedlist_t *read_transactions(FILE *fd) {
	/* This function should look awfully similar to read_accounts <lazy>*/
	
	//
	// !!TODO!!
	// Validate file before reading it
	//
	if (fd == NULL) {
		if (debug) puts("read_transactions(): File argument is NULL");
		return NULL;
	}
	char str[512];						//tmp string to write file line to
	linkedlist_t *list = create_linkedlist();
	if (debug) puts("begin reading transactions");
	while(fgets(str,512,fd) != NULL) {
		//handle creating hashtable
		
		long int *timestamp = malloc(sizeof(long int));
		char *transaction_string = malloc(sizeof(char) * transactionBufferSize);
		short transaction_type;
		char *company1 = malloc(sizeof(char) * charBufferSize);
		char *company2 = malloc(sizeof(char) * charBufferSize);
		double *value = malloc(sizeof(double));
		/*check that everything is a-okay*/
		if (debug) printf("scanning: %s\n", str);
		if(sscanf(str,"%ld %s %s %s %lf", timestamp, transaction_string, company1, company2, value) == EOF) { 
			if (debug) puts("sscanf::read_transactions() failed on case 1"); 
		}
		else {
			if (debug) puts("sscanf::read_transactions() successfully read");
		}
		
		
		//
		// Company1 and Company2 are allowed to be NULL {linkedlist.h}
		//
		if (company1 == NULL) { if (debug) puts("read_transactions(): sscanf produced NULL company1"); }
		if (company2 == NULL) { if (debug) puts("read_transactions(): sscanf produced NULL company2"); }
		if (timestamp == NULL) { if (debug) puts("read_transactions(): sscanf produced NULL timestamp"); }
		if (transaction_string == NULL) { if (debug) puts("read_transactions(): sscanf produced NULL transaction_type"); }
		if (value == NULL) { if (debug) puts("read_transactions(): sscanf produced NULL value"); }
		
		//Parse transaction_type
		if (transaction_string != NULL) {
			if (strcmp(transaction_string, "ADD") == 0) {
				transaction_type = 0;
				//fix value becoming company2
				if (sscanf(company2, "%lf", value) < 0) {
					if (debug) puts("read_transactions(): failed to fix company2 bug on type 1");
				}
				company2 = malloc(sizeof(char));
			}
			else if (strcmp(transaction_string, "REMOVE") == 0) {
				transaction_type = 1;				
			}
			else if (strcmp(transaction_string, "TRANSFER") == 0) {
				transaction_type = 2;
			}
			else {
				if (debug) puts("read_transactions(): failed to parse transaction_string");
				transaction_type = -1;
			}
			free(transaction_string);
		}
		
		if (timestamp != NULL && value != NULL) {
			node_t *node = create_node(*timestamp,transaction_type, company1, company2, *value);
			if (node == NULL) { if (debug) puts("read_transactions(): node is NULL"); continue; }
			if (add_node(list, node) != 0) {
				if (debug) puts("read_transactions(): add_node failed to add!");
				continue;
			}
			else {
				//hd = short int
				if (debug) printf("Added: %ld, type: %hd, %s, %s, %lf\n", *timestamp, transaction_type, company1, company2, *value);
				free(timestamp);
				if (company1 != NULL) free(company1);
				if (company2 != NULL) free(company2);
				free(value);
			}
		}
	}
	return list;
	/*</lazy>*/
}

int apply_transactions(linkedlist_t *transactions, hashtable_t *accounts) {
	if (transactions == NULL) {
		if (debug) puts("apply_transactions(): Transactions argument is NULL");
		return -1;
	}
	if (accounts == NULL) {
		if (debug) puts("apply_transactions(): Accounts argument is NULL");
		return -1;
	}
	
	//Iterate through list
	node_t* currNode;
	currNode = transactions->head;
	int transCount = 0;
	while(currNode != NULL) {
		if (currNode->transaction_type == 0) {
			//ADD 'company1' 'value'
            //Add 'company1' to the account hashtable with a value of 'value'
			if (currNode->value < 0) {
				if (debug) puts("apply_transactions(): ADD value is negative. ILLEGAL");
				return -1;
			}
			if (currNode->company1 == NULL) {
				if (debug) puts("apply_transactions(): ADD company1 does not exist. ILLEGAL");
				return -1;
			}
			if (set(accounts, currNode->company1, currNode->value) == 0) {
				if (debug) puts("successfully completed transaction");
				transCount++;
			}
			else {
				if (debug) printf("Transaction: ADD %s, %lf\n", currNode->company1, currNode->value);
				if (debug) puts("failed to add ADD transaction, set() failed");
				return -1;
			}
		}
		else if (currNode->transaction_type == 1) {
			//REMOVE 'company1'
			//Remove 'company1' from the hashtable if it exists, error if it doesn't
			if (currNode->company1 == NULL) {
				if (debug) puts("apply_transactions(): REMOVE company1 does not exist. ILLEGAL");
				return -1;
			}
			if (remove_key(accounts, currNode->company1) == 0) {
				if (debug) puts("Successfully completed transaction");
				transCount++;
			}
			else {
				if (debug) printf("Transaction: REMOVE %s \n", currNode->company1);
				if (debug) puts("failed to add REMOVE transaction, remove_key() failed");
				return -1;
			}
		}
		else if (currNode->transaction_type == 2) {
			//TRANSFER 'company1' 'company2' 'value'
			//Transfer 'value' from the account of 'company1' into the account of 'company2'
			// CHECK IF ACCEPTABLE
			if (currNode->value < 0) {
				if (debug) puts("apply_transactions(): TRANSFER value is negative. ILLEGAL");
				return -1;
			}
			if (currNode->company1 == NULL) {
				if (debug) puts("apply_transactions(): TRANSFER company1 does not exist. ILLEGAL");
				return -1;
			}
			if (currNode->company2 == NULL) {
				if (debug) puts("apply_transactions(): TRANSFER company2 does not exist. ILLEGAL");
				return -1;
			}
			//Check if company1 exists
			if (key_exists(accounts, currNode->company1) != 1) {
				if (debug) puts("apply_transactions(): Company1 does not exist");
				return -1;
			}
			//Check if company2 exists
			if (key_exists(accounts, currNode->company2) != 1) {
				if (debug) puts("apply_transactions(): Company2 does not exist");
				return -1;
			}			
			
			//CHECK IF there's enough money in Company1's account
			double *tmp = malloc(sizeof(double));
			get(accounts, currNode->company1, tmp);
			if (*tmp < currNode->value) {
				if (debug) puts("apply_transactions(): transaction failed because there are insufficient funds");
				if (debug) printf("Has: %lf, requested: %lf\n", *tmp, currNode->value);
				free(tmp);
				return -1;
			}
			free(tmp);
			
			if (set(accounts, currNode->company2, currNode->value) == 0) {
				if (set(accounts, currNode->company1, (-1 * currNode->value)) == 0) {
					if (debug) puts("Successfully completed transaction");
					transCount++;
				}
				else {
					if (debug) puts("apply_transactions(): TRANSFER company1 failed to subtract funds");
					return -1;
				}
			}
			else {
				if (debug) puts("apply_transactions(): TRANSFER company2 failed to add funds");
				return -1;
			}
		}
		else {
			//NULL
			if (debug) puts("apply_transactions(): NULL transaction found. ILLEGAL");
			return -1;
		}
		currNode = currNode->next;
	}
	return transCount;
}