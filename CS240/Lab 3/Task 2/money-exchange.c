#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

void convert(int type, double amount, double rate);
int get_type(char* string);

void convert(int type, double amount, double rate) {
	printf("%.2f %s is %.2f %s\n", amount, type == 1 ? "dollars" : "euros", amount * rate, type == 1 ? "euros" : "dollars");
}

int get_type(char* string) {
	int i, c;
	for (i = 0, c = string[0]; c != '\0'; c = string[i]) {
		if (c >= 'A' && c <= 'Z') {
			string[i] -= 'A' - 'a';
		}
	}
	return !strcmp(string, "dollar") ? 1 : !strcmp(string, "euro") ? 2 : 0;
}

int main(int argc, char** argv) {
        //assert(argc == 2 && argc ==4);
	if (argc == 4) {
		int type = get_type(argv[1]);
		if (type == 0) {
			printf("%s is an invalid currency type. Use dollar or euro.\n", argv[1]);
			return 1;
		}
		convert(type, atof(argv[2]), atof(argv[3]));
	}

	if (argc == 2) {
		FILE* fd;
		fd = fopen(argv[1], "r");
		if (fd == NULL) {
			printf("Could not open %s\n", argv[1]);
			return 1;
		}
		char * typestring = (char*)malloc(16 * sizeof(char));
		double amount, rate;
		int matches, type;
		
		while (!feof(fd)) {
			matches = fscanf(fd, "%s %lf %lf\n", (char *)&typestring, &amount, &rate);
			if (matches != 3) {
				printf("Line was not formed correctly.\n");
				continue;
			}
			type = get_type(typestring);
			if (type == 0) {
				printf("%s is an invalid currency type. Use dollar or euro.\n", typestring);
				continue;
			}
			convert(type, amount, rate);
		}
		free((void *)typestring);
	}


	if (argc == 2 && argc != 4) {
		printf("Usage:\n\tmoney-exchange [dollar|euro type] [double amount] [double rate]\n");
		printf("\tmoney-exchange [FILE]\n");
		printf("Examples:\n\tmoney-exchange dollar 10.50 0.92\n");
		printf("\tmoney-exchange euro 5.99 1.09\n");
		printf("\tmoney-exchange prices.txt\n");
		return 1;
	}
	return 0;
}


