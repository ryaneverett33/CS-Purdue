#include "MyVector.h"
#include <stdio.h>

/*******************************************************
 * For the detailed Task description, go to MyVector.h *
 *******************************************************/
/********* Implement the functions in this file ********/

unsigned int vector_size;
int *data;

  /* ========================= TASK1 STARTS HERE: =========================   *
   * Implement the following 3 functions in MyVector_fxns.cpp file.           *
   * Remember to use the MyException class wherever required.                 */

  /* Get the size of the vector                                               *
   * Return:                                                                  *
   *   The maximum number of elements `data` can hold                         */
  unsigned int MyVector::get_size() const {
	  return vector_size;
  }

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
  bool MyVector::get_num_at_idx(unsigned int index, int *ptr_num) const throw(MyException) {
	  if (index >= vector_size) {
		  throw MyException();
	  }
	  if (ptr_num == NULL) {
		  return false;
	  }
	  int num;
	  try {
		  num = data[index];
	  }
	  catch (exception e) {
		  throw MyException();
	  }
	  *ptr_num = num;
	  return true;
  }
  
  /* Set the integer `value` a particular `index` of data                     *
   * Return values:                                                           *
   * On success,                                                              *
   *   return true and                                                        *
   *   `value` is assigned to the element at the given `index`                *
   * For invalid index,                                                       *
   *   causes MyException                                                     *
   * NOTE: The caller of the function will handle the exception.              */
  bool MyVector::set_num_at_idx(unsigned int index, int value) throw(MyException) {
	  if (index >= vector_size) {
		  throw MyException();
	  }
	  try {
		  data[index] = value;
		  return true;
	  }
	  catch (exception e) {
		  throw MyException();
	  }
	  return false;
  }