/*******************************************************
 * For the detailed Task description, go to MyVector.h *
 *******************************************************/
 #ifndef  _MYEXCEPTION_H
 #define  _MYEXCEPTION_H

#include <iostream>
#include <exception>

using namespace std;

class MyException: public exception
{
	public:
	  virtual const char* what() const throw()
  	{
	  	return "Requested index is out of the bounds\n";
	  }
};

#endif /* _MYEXCEPTION_H */
