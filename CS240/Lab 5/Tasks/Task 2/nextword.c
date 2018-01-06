#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

/*
 *  This function returns the next word in the string *cptr.
 *  When the *cptr reaches the NULL character '\0', 
 *  the function returns NULL.
 *
 *  The returned memory space is allocated (malloc) by this function.
 *  For example, if *cptr is "abc def", you should allocate a memory space,
 *  copy the string "abc" to it, and return it.
 *  It is the caller's responsibility to free the space.
 *
 *  In addition, you have to update *cptr to point to the space that
 *  have not been parsed. 
 *  For example, if *cptr is "abc def", you should update
 *  the *cptr to point to the space character between "abc" and "def".
 *
 */

int len(char * word) {
	int len = 0;
	while (*word != 0) {
		len++;
		word++;
	}
	return len;
}
char *nextword(char **cptr)
{
	//char * stringy = (char *)*cptr;
	char * newStringy = malloc(1000);
	int index = 0;
	int letterCount = 0;

	while (**cptr != 0) {
		//printf("cptr: %c\n", **cptr);
		if (**cptr == ' ' || **cptr == '\r' || **cptr == '\t' || **cptr == '\n') {
			//evaluate space
			if (letterCount == 0) {
				//skip space
				*cptr = *cptr + 1;
			}
			else {
				newStringy[index] = '\0';
				letterCount = 0;
				*cptr = *cptr - 1;
				break;
			}	
		}
		else {
			//build word
			newStringy[index] = **cptr;
			index++;
			letterCount++;
			*cptr = *cptr + 1;
		}
	}
	if (**cptr == 0) {
		if (letterCount > 0) {
			//evaluate last word
			//printf("Evaluating last word\n");
			newStringy[index] = '\0';
		}
		else {
			//printf("returning null\n");
			return NULL;
		}
	}
	else {
		*cptr = *cptr + 1;
	} 
    return newStringy;
}

/*
 *  Do NOT change any of the lines between here and the end of the file
 */ 

int main(int argc, char *argv[])
{
    char *word = NULL;
    unsigned int count = 0;
    char *usage = "Usage: nextword \"string\"\n";
    char *cptr = NULL;

    if (argc != 2) {
        printf("%s", usage);
        exit(1);
    }

    cptr = argv[1];
    while( (word =  nextword(&cptr)) != NULL) {
        printf("%d: \"%s\" | \"%s\"\n", count++, word, cptr);
        free(word);
    }
    
    return 0;
}

