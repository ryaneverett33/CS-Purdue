#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <sys/stat.h>
#include <unistd.h>
#include "../h/global.h"

/*------------------------------------------------------------------------
 * readln - read from stdin until newline or EOF, or buffer is full.
 * Flush to newline or EOF and return on full buffer. Returns data length.
 *------------------------------------------------------------------------
 */
int
readln (char *buff, int buffsz)
{
    char  *bp = buff, c;
    int  n;

    while (bp - buff < buffsz &&
           (n = read (STDIN_FILENO, bp, 1)) > 0) {
        if (*bp++ == '\n')
            return (bp - buff);
    }

    if (n < 0)
        return -1;

    if (bp - buff == buffsz)
        while (read (STDIN_FILENO, &c, 1) > 0 && c != '\n');

    return (bp - buff);
}

enum Commands parseCommand(char * string, int len) {
    if (len < 4) {
        return INVALID;
    }
    else {
        if (strncmp(string, "OPEN", 4) == 0) {
            return OPEN;
        }
        else if (strncmp(string, "READ", 4) == 0) {
            return READ;
        }
        else if (strncmp(string, "BACK", 4) == 0) {
            return BACK;
        }
        else if (strncmp(string, "CLOS", 4) == 0) {
            return CLOS;
        }
        else {
            return INVALID;
        }
    }
}
//return 10 from 'READ 10\n'
int getIntArgument(char * string, int stringLen) {
    if (stringLen < 7) {
        //must be followed by newline
        return -1;
    }
    int newLength = stringLen - 5;      //remove 'XXXX '
    char * raw_arg_string = (char*)malloc(sizeof(char) * (newLength));
    char * pointer = string;
    pointer += 5;   //point to '1'
    strncpy(raw_arg_string, pointer, newLength);
    raw_arg_string[newLength] = 0;        //null-terminate
    int value = atoi(raw_arg_string);
    free(raw_arg_string);
    return value;
}

int getStringLen(char * string) {
    bool count = true;
    int i = 0;
    while(count) {
        if (string[i] == 0)
            return i;
        //printf("%c(%d) ", string[i], i);
        //fflush(stdout);
        i++;
    }
}
int getIntLength(int argument) {
    int offset = 0;
    int value = argument;
    if (argument < 0) {
        offset++;
        int value = -1 * argument;
    }
    if (value < 10)
        return 1 + offset;
    else if (value < 100)
        return 2 + offset;
    else if (value < 1000)
        return 3 + offset;
    else if (value < 10000)
        return 4 + offset;
    else if (value < 100000)
        return 5 + offset;
    else if (value < 1000000)
        return 6 + offset;
    else if (value < 10000000)
        return 7 + offset;
    else if (value < 100000000)
        return 8 + offset;
    else if (value < 1000000000)
        return 9 + offset;
    else if (value < 10000000000)
        return 10 + offset;
    else
        return 11;
}
bool isValidRequest(struct prompt_res * result) {
    if (result == NULL) {
        return false;
    }
	if (result->command == INVALID)
		return false;
	switch (result->command) {
		case OPEN:
			//takes a filename and filenameLen argument
			return (result->filename != NULL && result->filenameLen != -1);
		case READ:
		case BACK:
			//takes a int argument
			return (result->argument != -1);
		case CLOS:
			//doesn't take any arguments
			return true;
	}
	return false;
}
int getFileSize(char * filename) {
    struct stat st;
    stat(filename, &st);
    return st.st_size;
}
//check if filename contains '..' && return false if it does
bool doesFileExist(char * filename) {
    if (strstr(filename, "..") != NULL) {
        return false;
    }
    struct stat st;
    return (stat(filename, &st) == 0);
}
bool isFilenameEqual(char * filename1, char * filename2) {
    return strcmp(filename1, filename2) == 0;
}
/*int ClampLower(int lowerbound, int value) {
    if (value < lowerbound)
        return lowerbound;
    else
        return value;
}*/