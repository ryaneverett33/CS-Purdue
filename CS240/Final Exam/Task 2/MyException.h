/*******************************************************
 * For the detailed Task description, go to MyVector.h *
 *******************************************************/

#include <iostream>
#include <exception>

#ifndef _MYEXCEPTION_H
#define _MYEXCEPTION_H

using namespace std;

class MyException: public exception
{
	public:
	  virtual const char* what() const throw()
	  {
		  return "Vector lengths are not equal\n";
  	}
};

#endif /*_MYEXCEPTION_H */
