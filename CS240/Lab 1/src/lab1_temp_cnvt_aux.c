/*
 * lab1_temp_cnvt_aux.c -- Helper functions for 2nd introductory program
 *
 *  F_to_C takes a Fahrenheit temperature as a float, and returns
 *	the corresponding Centrigrade temperature as function value
 *
 *  C_to_F takes a Centrigrade temperature as a float, and returns
 *	the corresponding Fahrenheit temperature as a function value
 *
 *  There are no side-effects or other changes.
 *
 */

#include "lab1_temp_cnvt_hdr.h"

/*
 *  TRatio is a real constant with the conversion multiplier.
 *  TDiff is the real constant difference in scale.
 *
 *  The values are chosen to allow conversion between Fahrenheit and
 *    Centigrade temperatures.
 *
 */

const float TRatio = 5.0/9.0;  /* We'll start with C -> F */
const float TDiff = 32.0; 

float F_to_C (float fahr)
{
	float temp;

	temp = fahr - TDiff;
	temp = temp * TRatio;

	return temp;
}

float C_to_F (float cent)
{
        float temp;

        temp = cent / TRatio;
        temp = temp + TDiff;

        return temp;
}

