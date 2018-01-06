#include <iostream>
#include "MyException.h"
using namespace std;
/*
  * ================================ TASK-1 ================================  *
  * The MyVector class has prototypes for the following functions, but the    *
  * implementation of these are missing. The functions are                    *
  *   1. get_size                                                             *
  *   2. get_num_at_idx                                                       *  
  *   3. set_num_at_idx                                                       *
  * Your task is to implement these functions in MyVector_fxns.cpp file       *
  * NOTE: Use the exception wherever necessary.                               *
  
  * Few RULES to keep in mind for TASK-1                                      *
  * RULE 1: DO NOT MODIFY THIS FILE                                           *
  * RULE 2: Add your code in MyVector_fxns.cpp                                *
  * RULE 3: Make sure your code compiles using the Makefile provided.         *
  *         Compilation error will give you no points.                        *
*/



class MyVector
{
  private:
    /* Maximum number of elements the data can hold */
    unsigned int  vector_size;

    /* Dynamically created array of integers. Initial value of each element is 0 */
    int           *data;


  public:
    /* Sets the vector_size to 0 and data to NULL */
    MyVector();

    /* Dynammically allocates an array of `n` integers and stores the pointer in 
     * member variable `data`*/
    MyVector(unsigned int n);

    /* Creates a replica of the object `copy`. The created object will have its 
     * newly created memory, not just a copy of the pointer. */
    MyVector(const MyVector& copy);

    /* Destructs the object deleting any allocated memory */
    ~MyVector();

    /* Prints the vector */ 
    void print();

  /* ========================= TASK1 STARTS HERE: =========================   *
   * Implement the following 3 functions in MyVector_fxns.cpp file.           *
   * Remember to use the MyException class wherever required.                 */

  /* Get the size of the vector                                               *
   * Return:                                                                  *
   *   The maximum number of elements `data` can hold                         */
  unsigned int  get_size() const; 

  /* Get the element at a particular `index` in data.                         *
   * Return:                                                                  *
   * On success,                                                              *
   *    return true and                                                       *
   *    element at `index` is copied into the variable pointed by ptr_num.    *
   * For invalid index                                                        *
   *    causes MyException                                                    *
   * For other errors                                                         *
   *    return false                                                          *
   * NOTE: The caller of the function will handle the exception.              */
  bool get_num_at_idx(unsigned int index, int *ptr_num) const throw(MyException);
  
  /* Set the integer `value` a particular `index` of data                     *
   * Return values:                                                           *
   * On success,                                                              *
   *   return true and                                                        *
   *   `value` is assigned to the element at the given `index`                *
   * For invalid index,                                                       *
   *   causes MyException                                                     *
   * NOTE: The caller of the function will handle the exception.              */
  bool set_num_at_idx(unsigned int index, int value) throw(MyException);

  /* ========================= TASK1 ENDS HERE: =========================   */

};

