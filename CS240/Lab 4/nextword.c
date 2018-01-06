#define true 1
#define false 0

#include <stdio.h>
#include <stdlib.h>

//
// Separates the file into words
//

#define MAXWORD 200
char word[MAXWORD];
int wordLength = 0;

// It returns the next word from fd.
// If there are no more more words it returns NULL. 
char * nextword(FILE * fd) {
  	int c;
	int canContinue = true;
	wordLength = 0;

	// While it is not EOF read char
		// While it is not EOF and it is a non-space char
		// store character in word.
		// Include an assert statement that the current word is not MAXWORD characters long or longer
		// if char is not in word return word so far.
		//
	// Return null if there are no more words
	if (fd == NULL) {
		printf("Could not open file!");
		//fclose(fd);
		return NULL;
	} 
	while(canContinue) {
		if((c = fgetc(fd)) == EOF) {
			canContinue = false;
			//wordLength = 0;
			break;
		}
		else if (c == ' ' || c == '\n' || c == '\t' || c == '\r') {
			if (wordLength == 0) {
				//word[0] = '\0';
				//return word;
				continue;
			}
			canContinue = false;
		}
		else {
			canContinue = true;
			word[wordLength] = c;
			wordLength++;
		}
		
	}
	if (wordLength > 0) {
		word[wordLength] = '\0';
		//fclose(fd);
		return word;
	}
	//fclose(fd);
	return NULL;
}

