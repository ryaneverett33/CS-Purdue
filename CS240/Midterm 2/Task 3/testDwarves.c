#include <stdio.h>
#include <stdlib.h>
#include "dwarves.h"

/*
char *DaysOfW[8] = { 
	"No day", "Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"
};
*/
void printLines(char **freeDays) {
	int i;
	for (i = 0; i < MAXDWARVES * 2; i++) {
		printf("%d: %s\n", i, freeDays[i]);
	}
}
int main() {
	char *Roster[12] = {
		"Doc", "Grumpy", "Happy", "Sleepy", "Bashful", "Sneezy", "Dopey", "Grouchy", "Smiley", "Lazy", "Chubby", "Bombur"
	};
	char **sched = init_schedule(Roster);
	int res;
	//TEST hard_working !!
	print_schedule(sched);
	puts("");
	res = request_day(sched,"Doc","Tuesday");
	if (res != 0) {
		printf("Request Day off failed for 'Doc' on 'Tuesday' with value %d\n",res);
	}
	else {
		puts("Succesfully requested off for Doc");
	}
	res = request_day(sched,"Jarrom","Tuesday");
	if (res != 1) {
		printf("Request Day off failed for 'Jarrom' on 'Tuesday' with value %d\n",res);
	}
	else {
		puts("Successfully tested dwarve not exist");
	}
	//request another day off
	
	res = request_day(sched,"Grumpy","Wednesday");
	if (res != 0) {
		printf("Request Day off failed for 'Grumpy' on 'Wednesday' with value %d\n",res);
	}
	else {
		puts("Succesfully requested off for Grumpy");
	}
	
	//request another day off
	res = request_day(sched, Roster[5], "Friday");
	if (res != 0) {
		printf("Request Day off failed for 'Sneezy' on 'Friday' with value %d\n",res);
	}
	else {
		puts("Succesfully requested off for Sneezy");
	}
	print_schedule(sched);
	puts("Test two");
	char **sched2 = init_schedule(Roster);
	request_day(sched2,"Doc","Tuesday");
	request_day(sched2,"Grumpy","Tuesday");
	request_day(sched2,"Happy","Tuesday");
	request_day(sched2,"Sleepy","Tuesday");
	request_day(sched2,"Bashful","Tuesday");
	request_day(sched2,"Sneezy","Tuesday");
	request_day(sched2,"Dopey","Tuesday");
	request_day(sched2,"Grouchy","Tuesday");
	print_schedule(sched2);
	res = request_day(sched2,"Smiley","Tuesday");
	if (res != 3) {
		printf("Request Day off failed for 'Smiley' on 'Tuesday' with value %d\n", res);
	}
	else {
		puts("Successfully tested request off when unavailable");
	}
	puts("Test hard working");
	int i;
	int **hwork = malloc(sizeof(int) * 2);
	res = hard_working(sched2,hwork);	//should be 4
	printf("hard_working returned %d\n",res);
	for (i = 0; i < res; i++) {
		printf("%d\n", (int)hwork[i]);
	}
	return 1;
}