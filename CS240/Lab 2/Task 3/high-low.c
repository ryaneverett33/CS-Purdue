#include <stdio.h>
//

int main(int argc, char **argv) {
	 printf("Welcome to the High Low game...\n");
	 int low, high, mid, innerLoop = 1, outerLoop = 1;
	 char response;
	 while (outerLoop) {
	 	printf("Think of a number between 1 and 100 and press <enter>");
		getchar();	//Surprise, gotta clear the buffer
		low = 1;
		high = 100;
		while (innerLoop) {
			//getchar();
			mid = (low + high)/2;
			printf("Is it higher than %i? (y/n)\n", mid);
			scanf("%c", &response);
			if (response == 'y') {
				low = mid + 1;	
			}
			else if (response == 'n') {
				high = mid - 1;	
			}
			if (high < low) {
				//Game has won
				printf("\n");
				printf(">>>>>> The number is %i\n", low);
				printf("\n");
				innerLoop = 0;	//Denote that the innerLoop has finished
			}
			else {
				getchar();	//Clear the buffer
			}
		}
		getchar();	//Clear the buffer
		printf("Do you want to continue playing (y/n)?\n");
		scanf("%c", &response);
		if (response == 'n') {
			outerLoop = 0;		//Denote that the mainLoop has finished
			printf("Thanks for playing!!!\n");
		}
		else {
			outerLoop = 1;		//Let's do it again
			innerLoop = 1;
			getchar();		//Buffer clearing (again)
		}
	 }
  	return 0;
}

