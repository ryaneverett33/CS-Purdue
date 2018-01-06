/*******************************************************
 * For the detailed Task description, go to MyVector.h *
 *******************************************************/

#include <iostream>
#include <exception>
#include <stdlib.h>
#include "MyVector.h"
#include "MyException.h"

using namespace std;

#define PASS 0

/*
 * Assignment of MyVector Objects. 
 * A = [1, 2, 3]
 * B = A;
 * Contents of A gets copied to B (deep-copy).
 */
int test_assign0() 
{
  int     array[5] = {1, 2, 3, 4, 5};

  MyVector  a(5, array);
  MyVector  b;

  b = a;

  b.print();
  return PASS; 
}

/* Chained Assignment
 * Example: 
 *  A = [1, 2, 3]
 *  B = C = D = A;
 *  Now A, B, C, D should be [1, 2, 3]
 */
int test_assign1() { 
  int     array[5] = {1, 2, 3, 4, 5};

  MyVector  a(5, array);
  MyVector  b,c,d;
  
  b=c=d=a; 

  b.print();
  return PASS; 
}

/* Vector-Vector multiplication. Example is given below.
 *
 * If vectors A and B are of same length then
 * Each element of A will get multiplied with 
 * corresponding element in vector B
 *  Example: 
 *  A = [1, 2, 3]
 *  B = [4, 3, 100]
 *  C = a*b; // => [1*4, 2*3, 3*100]
 *
 *  Now, C will be [4, 6, 300]
 */

int test_mult() { 
  int     array[5] = {1, 2, 3, 4, 5};

  MyVector  a(5, array);
  MyVector  b(5, array);
  MyVector  c(5, NULL);

  try 
  {
    c = (a * b);
    c.print();
  } 
  catch (MyException &e)
  {
    cout << e.what();
  } 

  return PASS; 
}


/* Scalar-Vector Multiplication. 
 * A scalar value is multiplied to a vector on the left. 
 * Example: 
 *  A = [1, 2, 3]
 *  scalar = 4
 *  B = (scalar * b); => Observe that the scalar is on the LEFT of *, not right.
 *  Now, B will be [4, 8, 12].
 */
int test_sc_mult() 
{ 
  int     array[5] = {1, 2, 3, 4, 5};

  MyVector  a(5, array);
  a = (-1 * a);
  a.print();

  return PASS; 
}

/* Exception Handling. 
 * Vector of length 3 is multiplied with Vector of length 4.  
 * Example: 
 *  A = [1, 2, 3]
 *  B = [9, 8, 7, 6]
 *  C = A * B
 *  Results in exception of type MyException.
 */
int test_exception() 
{ 
  int     array0[5] = {1, 2, 3, 4, 5};
  int     array1[4] = {1, 2, 3, 4};

  MyVector  a(5, array0);
  MyVector  b(4, array1);

  try
  {
    MyVector c = (a * b);
    c.print();
  }

  catch(MyException &e)
  {
    cout << e.what();
  }

  return PASS; 
}


int main(int argc, char *argv[])
{
  if (argc != 2)
  {
    printf("Usage: ./task2 <testcase Number>\n");
    return 0;
  }
  switch (atoi(argv[1]))
  {
    case 0:
      test_assign0(); /* Assignment test */
      break;
  
    case 1: 
      test_assign1(); /* Chained Assignment test*/
      break;
    
    case 2: 
      test_mult(); /* Vector-Vector multiplication*/
      break;
    
    case 3:
      test_sc_mult(); /*Scalar-Vector multiplication*/
      break;
    
    case 4:
      test_exception(); /* Exception test */
      break;
    
    default:
      break;
  }

  return 0;
}
