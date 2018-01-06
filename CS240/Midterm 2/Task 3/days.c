#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include "dwarves.h"

char *DaysOfW[8] = { 
	"No day", "Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"
};
char *Roster[12] = {
	"Doc", "Grumpy", "Happy", "Sleepy", "Bashful", "Sneezy", "Dopey", "Grouchy", "Smiley", "Lazy", "Chubby", "Bombur"
};

char ** init_schedule(char *working[MAXDWARVES]) {
	if (working == NULL) {
		return NULL;
	}
	char **workingCopy = malloc(sizeof(char *) * MAXDWARVES);
	char **schedule = malloc(sizeof(char *) * MAXDWARVES * 2);
	int i, didSwap;
	//puts("copying");
	for (i = 0; i < MAXDWARVES; i++) {
		char *dest = malloc(sizeof(char *));
		strcpy(dest,working[i]);
		workingCopy[i] = dest;
	}
	//alphabetize workingCopy
	do {
		didSwap = 0;
		for (i = 1; i < MAXDWARVES; i++) {
			if (strncmp(workingCopy[i-1],workingCopy[i],2) >= 1) {
				//swap strings
				didSwap = 1;
				char *foo = workingCopy[i-1];
				workingCopy[i-1] = workingCopy[i];
				workingCopy[i] = foo;
			}
		}
	}
	while (didSwap);
	for (i = 0; i < MAXDWARVES * 2; i++) {
		if (i % 2 == 0) {
			//name
			schedule[i] = workingCopy[i/2];
		}
		else {
			//No day
			schedule[i] = DaysOfW[0];
		}
	}
	return schedule;
}

int request_day(char **freeDays, char *dwarf, char *day) {
	//No argument will be null
	//The return value is 0 if the schedule request is granted and the schedule is updated.
	//The return value is 1 if the name of the dwarf doesn't match one in the schedule
	//The return value is 2 if the day off doesn't match an entrya day of the week as in DaysOfW
	//The return value is 3 if too many dwarves already have that day off. AT LEAST FOUR MUST BE WORKING
	int i, doesExist = 0, dayMatch = 0, index = 0, dwarvesOnDay = 0;
	//check if dwarf exists strcmp == 0
	for (i = 0; i < MAXDWARVES * 2; i++) {
		if (i % 2 == 0) {
			//printf("%s versus %s. i = %d\n", dwarf, freeDays[i/2], i);
			if (strcmp(dwarf,freeDays[i]) == 0) {
				//puts("Dwarf exists");
				index = i + 1;			//Assign location of dwarf so we don't have to look it up again
				doesExist = 1;
				break;
			}
		}
		else {
			continue;
		}
	}
	if (!doesExist) return 1;
	
	for (i = 1; i < 8; i++) {
		if (strcmp(day,DaysOfW[i]) == 0) {
			//puts("days match");
			dayMatch = 1;
			break;
		}
	}
	if (!dayMatch) return 2;
	//dwarf exists and so does day, check if they can request off
	for (i = 0; i < MAXDWARVES * 2; i++) {
		if (i % 2 == 1) {
			if (strcmp(day,freeDays[i]) == 0) {
				dwarvesOnDay++;
			}
		}
		else {
			continue;
		}
	}
	//must be at least 4 working, so leave a space for if dwarf doesn't work
	if (dwarvesOnDay <= 7) {
		//can get off.
		freeDays[index] = day;
		return 0;
	}
	else {
		//can't get off
		return 3;
	}
}

int hard_working(char **freeDays, int **hwork) {
	int num = 0, i = 0;
	hwork = malloc(sizeof(int) * 1);		//indexes of each dwarf without a day off = "No day"
	for (i = 0; i < MAXDWARVES * 2; i++) {
		if (strcmp(freeDays[i],DaysOfW[0]) == 0) {
			//add the index to the array
			num++;
			hwork = realloc(freeDays,num);
			hwork[num - 1] = i;
		}
	}
	return num;
}

void print_schedule (char **freeDays) {
	//S_format = "Dwarf %s has %s off.\n"
	int i =0;
	for (i = 0; i < MAXDWARVES * 2; i++,i++) {
		printf(S_format,freeDays[i],freeDays[i+1]);
	}
}