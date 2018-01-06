/*
 * lab1_temp_cnvt_main.c -- Main program file for 2nd Introductory program
 *
 *  The main program takes a single F or C on the command line when started
 *   to indicate the kind of conversion to be performed.  It then takes
 *   input of a floating point value from the user.
 *   The program outputs a message, the converted temperature, and exits.
 *
 *   You do NOT need to understand what everything in this program does but
 *   make the attempt!
 *
 */

#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include "lab1_temp_cnvt_hdr.h"

const char Usage[] = "Usage: temp_cnvt.out [F | C]\nThen enter a temperature.\n";

int main (int argc, char *argv[])
{
    char selection;  /* to process the temperature option */
    float intemp, outtemp;

/* 
 * We will first check to be sure that only one argument was given, and
 *  that the argument was a single letter.  
 *
 */

    if (argc != 2 || strlen(argv[1]) > 1)  
    {
	fprintf(stderr, Usage);
	return -1;
    }

/*
 *  We will convert that letter to upper case.
 *  The conversion routine does nothing if the letter is already upper case.
 * 
 *  We then check to see if it is one of the two options.
 *
 */
    printf("Enter a temperature: ");

    selection = toupper(*argv[1]);   

    if (selection != 'F' && selection != 'C')
    {
	fprintf(stderr, Usage);
	return -1;
    }

/* 
 * Now we will get the input temperature, convert it, and print the output
 *
 */

    if (fscanf(stdin, "%f", &intemp) != 1)
    {
	fprintf(stderr, "Not a valid temperature!\n");
	return -1;
    }

    if (selection == 'C')
    {
	outtemp = C_to_F(intemp);
	printf("%.2f degrees C is %.2f degrees F.\n", intemp, outtemp);
    }
    else if (selection == 'F')
    {
	outtemp = F_to_C(intemp);
	printf("%.2f degrees F is %.2f degrees C.\n", intemp, outtemp);
    }

    return 0;
}
