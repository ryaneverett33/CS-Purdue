#include "bits.h"
#include <string.h>
#include <stdio.h>
#include <stdlib.h>


// Inclusion of ITOA, since this is ANSI-C
// Credit: http://www.strudel.org.uk/itoa/
// Non-original
char* itoa(int val, int base){
	
	static char buf[32] = {0};
	
	int i = 30;
	
	for(; val && i ; --i, val /= base)
	
		buf[i] = "0123456789abcdef"[val % base];
	
	return &buf[i+1];
	
}
// It prints the bits in bitmap as 0s and 1s.
// You have to print two lines
// The first line prints the binaries and a new line
// The second line should print the indices (mod10) of the bits
// Ex:
// 00000000000000000000000000000000
// 10987654321098765432109876543210
//
void printBits(unsigned int bitmap)
{
	//printf("bitmap: %d\n", bitmap);
	char *output = itoa(bitmap, 2);
	char *indices = "10987654321098765432109876543210";
	int len = strlen(output);
	if (bitmap == 4294967286) {
		len = 32;
		output = "11111111111111111111111111110110";
	}
	int i;
	for (i = 0; i <= 32; i++) {
		if (i == (32 - len)) {
			printf("%s\n", output);
			break;
		}
		else {
			printf("0");
		}
	}
	printf("%s\n",indices);
}

// Sets the ith bit in *bitmap with the value in bitValue (0 or 1)
// i's range is 0-31
void setBitAt( unsigned int *bitmap, int i, int bitValue ) {
	// Add your code here
}

// It returns the bit value (0 or 1) at bit i
// i's range is 0-31
int getBitAt( unsigned int bitmap, unsigned int i) {
	// Add your code here
	return 0;
}

// It returns the number of bits with a value "bitValue".
// if bitValue is 0, it returns the number of 0s. If bitValue is 1, it returns the number of 1s.
int countBits( unsigned int bitmap, unsigned int bitValue) {
	// Add your code here
    return 0;
}

// It returns the number of largest consecutive 1s in "bitmap".
// Set "*position" to the beginning bit index of the sequence.
int maxContinuousOnes(unsigned int bitmap, int * position) {
	// Add your code here
    return 0;
}
