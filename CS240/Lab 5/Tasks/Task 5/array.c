#include <stdio.h>
#include <stdlib.h>

#include "array.h"

// Return sum of the array
// Return zero if inputs are invalid
double sumArray(int n, double * array) {
	if (n == 0 || array == NULL) {
		return 0;
	}
	double sum = 0;
	int i;
	for (i = 0; i < n; i++) {
		sum = sum + *array;
		array++;
	}
    return sum;
}

// Return maximum element of array
// If the inputs are invalid, return 0`
// Note: return its value, not its index
double maxArray(int n, double * array) {
	if (n == 0 || array == NULL) {
		return 0;
	}
	double max = 0;
	int i;
	for (i = 0; i < n; i++) {
		if (*array > max) {
			max = *array;
		}
		array++;
	}
    return max;
}

// Return minimum element of array
// If the inputs are invalid, return 0`
// Note: return its value, not its index
double minArray(int n, double * array) {
	if (n == 0 || array == NULL) {
		return 0;
	}
	double min = 0;
	int i;
	for (i = 0; i < n; i++) {
		if (*array < min) {
			min = *array;
		}
		array++;
	}
    return min;
}

// Find the position in the array of the first element 
// whose value is min<=x<=max.
// Return -1 if no element was found or the inputs are invalid
// Note: return the target's index, not its value
int findArray(int n, double * array, double min, double max) {
	if (n == 0 || array == NULL) {
		return -1;
	}
	int i;
	for (i = 0; i < n; i++){
		if (*array >= min && *array <= max) {
			return i;
		}
		array++;
	}
    return -1;
}

// reverse the elements in the array
// For example,
// an array with values 1,2,3,4,5 (double a[5]={1,2,3,4,5})
// should be converted into
// an array with values 5,4,3,2,1 (double b[5]={5,4,3,2,1})
// If the inputs are invalid, return without changing the array
void reverseArray(int n, double * array) {
    //copy array first
	if (n == 0 || array == NULL) {
		return;
	}
	double *copy = malloc(1000);
	int i;
	for (i = 0; i < n; i++) {
		*copy = *array;
		copy++;
		array++;
	}
	//reset position of pointers
	for (i = 0; i < n; i++) {
		array--;
	}
	copy--;
	
	//reverse array
	for (i = 0; i < n; i++) {
		*array = *copy;
		array++;
		copy--;
	}
}

// Print out each element in the array in the following format:
// For an array a[3]={4,3,5}
// the output would be:
// 0:4.000000
// 1:3.000000
// 2:5.000000
// Note that newline should be added at the end of each element.
// If the inputs are invalid, return without changing the array
void printArray(int n, double * array) {
    if (n == 0 || array == NULL) {
		return;
	}
	int i;
	for (i = 0; i < n; i++){
		printf("%d:%lf\n",i,*array);
		array++;
	}
}

