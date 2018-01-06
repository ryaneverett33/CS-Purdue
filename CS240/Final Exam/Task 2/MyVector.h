#include <iostream>

/*
  * ================================ TASK-2 ================================= *
  * The main() function performs various arithmetic operations on the objects *
  * of MyVector. But these operations are NOT yet defined in MyVector class.  *

  * Your task is the following:                                               *
  * 1. Find out the various arithmetic operators to be overloaded             *
  * 2. Declare the operator-overloading function prototypes in the MyVector.h *
  * 3. Implement the operator overloading functions in MyVector_fxns.cpp      *
  * 4. Identify exception cases and throw objects of MyException class        *
  * 5. Identify corner cases and handle them appropriately.                   *
  
  * ================================= HINT ================================== *
  * HINT1: Go through main() and testcases. Observe the compilation errors.   *
  * HINT2: You will define three operator overloading functions.              *
  
  * ================================ RULES ================================== *
  * RULES to keep in mind for TASK-2                                          *
  * RULE 1: Add your operator overloading function prototypes in              *
  *         MyVector.h file (this file)                                       *
  * RULE 2: Add your code in MyVector_fxns.cpp                                *
  * RULE 3: Make sure your code compiles using the Makefile provided.         *
  *         Compilation error will give you -NO POINTS-.                      *
  * ================================= END =================================== *
  * Good luck!
 */


using namespace std;

class MyVector {

  private:
    /* Maximum number of elements the data can hold */
    unsigned int  vector_size;

    /* Dynamically created array of integers. Initial value of each element is 0 */
    int           *data;

  
  public:
    /* Sets the `vector_size` to 0 and `data` to NULL */
    MyVector();

    /* Dynammically allocates an array of `n` integers and stores the pointer in 
     * member variable `data` */
    MyVector(unsigned int n);
  
    /* Dynammically allocates an array of `n` integers and stores the pointer in 
     * member variable `data`. 
     * If the `in_array` is NULL then 
     *    sets all elements of `data` to 0, 
     * else 
     *    copies each element of `in_array` into `data` 
     */
    MyVector(unsigned int size, int *in_array);

    /* Creates a replica of the object `copy`. The created object will have its 
     * own memory (dynamically allocated), not just a copy of the pointer. */
    MyVector(const MyVector& copy);

    /* Destructs the object deleting any allocated memory. */
    ~MyVector();

    /* Prints the vector */ 
    void print();

	friend MyVector operator * (MyVector const &vec, MyVector const &vec2);

	friend MyVector operator * (int num, MyVector const &vec);
	
	MyVector operator = (MyVector const &vec);
	
};

