#include <stdio.h>
#include <stdlib.h>
#include "io.h"

#define debug 0
#define error 1
#define good 0

int main(int argc, char** argv) {
	//./process <transaction_file> <account_in_file> <account_out_file>
	if (argc != 4) {
		//Account for executable name as first argument
		puts("Usage: <transaction_file> <account_in_file> <account_out_file>");
		return error;
	}
	
	FILE *transFile, *accountINFile, *accountOUTFile;
	transFile = fopen(argv[1], "r");
	if (transFile == NULL) {
		if (debug) puts("transFile is NULL. FATAL ERROR");
		return error;
	}
	accountINFile = fopen(argv[2], "r");
	if (accountINFile == NULL) {
		if (debug) puts("accountINFile is NULL. FATAL ERROR");
		return error;
	}
	accountOUTFile = fopen(argv[3], "w");
	if (accountOUTFile == NULL) {
		if (debug) puts("accountOUTFile is NULL. FATAL ERROR");
		return error;
	}
	hashtable_t *accounts = read_accounts(accountINFile);
	linkedlist_t *transactions = read_transactions(transFile);
	if (apply_transactions(transactions,accounts) < 0) {
		if (debug) puts("process::apply_transactions(): failed. FATAL ERROR");
		return error;
	}
	write_accounts(accountOUTFile, accounts);
	return good;
}