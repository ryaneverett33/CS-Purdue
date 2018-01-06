#include <stdio.h>
#include "circle.h"
#define Pi 3.14

int main(int argc, char **argv) {
        printf("Finding area and circumference of a circle given a radius\n");
        double radius;
	double area, circumference;
	char keepingOn;				//basically continue, but that was reserved
	while(1) {
		printf("Enter the radius and <enter>: ");
		scanf("%lf", &radius);
		if (radius < 0) {
			printf("Radius cannot be negative\n");
		}
		else {
			area = Pi * (radius * radius);
			circumference = 2 * Pi * radius;
			printf("Area is = %f \n", area);
			printf("Circumference is = %f \n", circumference);
		}
		getchar();		//Clearing that buffer
		printf("Do you want to continue? Type y/n and <enter>");
		scanf("%c", &keepingOn);
		if (keepingOn == 'n') {
			printf("Bye\n");
			return 0;
		}
	}
	return 0;
}

