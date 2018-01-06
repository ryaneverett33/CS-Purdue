#include <stdio.h>

int main(int argc, char **argv) {
        printf("Finding maximum among three numbers a,b and c\n");
        while(1) {
		int abc[3];
		int max, min;
		char response;
		printf("Type a and <enter>: ");
		scanf("%d", &abc[0]);
		printf("Type b and <enter>: ");
		scanf("%d", &abc[1]);
		printf("Type c and <enter>: ");
		scanf("%d", &abc[2]);

		if ((abc[0] > -1 && abc[0] < 101) && (abc[1] > -1 && abc[1] < 101) && (abc[2] > -1 && abc[2] < 101)){
			//printf("Arguments are valid\n");
			int i;
			for (i = 0; i < 3; i++) {
				if (i == 0) {
					max = abc[i];
					min = abc[i];
				}
				else { 
					if (abc[i] > max) {
						max = abc[i];
					}
					else if (abc[i] < min) {
						min = abc[i];
					}
				}
			}
			if (max == min) {
				printf("All three values are equal\n");
			}
			else {
				printf("maximum = %i\n", max);
				printf("minimum = %i\n", min);
			}
		}
		else {
			printf("Numbers are not in the correct range [0-100]\n");
		}
		getchar();	//Attempt to clear buffer
		printf("Do you want to continue? Type y/n and <enter>");
		response = getchar();
		if (response == 'n') {
			printf("Bye\n");
			break;
		}
	}
	return 0;
}

