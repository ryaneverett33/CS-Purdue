#include "Employee.h"

int Id;
char* Name;
double Salary;
	
/**
 * Constructor for the Employee
 * Parameters:
 *      id - Employee ID for this Employee
 *      name - Pointer to a character string containing this employee's name
 *      salary - Salary for this employee
 * Remarks:
 *      The constructor is called to initialize the memory of the object.
 *      It should perform appropriate copies of strings, and initialize
 *      various member variables as required.
 */

Employee::Employee(int id, char* name, double salary) {
	Id = id;
	Name = name;
	Salary = salary;
}


/**
 * Copy constructor, to make a new instance as a copy of another
 * Parameters:
 *      other - Constant reference to another Manager instance that we are copying
 * Remarks:
 *      The copy constructor is called to create a new instance as a copy
 *      of an existing instance. Copies should be 'deep' meaning that any
 *      underlying resources such as memory should also be copied over.
 */
Employee::Employee(const Employee& other) {
	Id = other.Id;
	Name = other.Name;
	Salary = other.Salary;
}

/**
 * Destructor for Employee
 * Remarks:
 *      The destructor is called when an instance of the class is deleted,
 *      either by calling 'delete' on a pointer or when a local copy on the
 *      stack is deleted when a function returns. The destructor must cleanup
 *      any memory or resources held by the object.
 */
Employee::~Employee() {
	Id = 0;
	Salary = 0;
	//delete Name;
}

/**
 * Copy assignment operator
 * Parameters:
 *      other - The other instance we are being assigned from
 * Returns:
 *      A reference to the current instance 'this' that was assigned to
 *      A copy assignment operator is invoked when an assignment is occuring,
 *      for instance Engineer a = b; where b is an existing Engineer instance.
 *      The operator should free any resources currently being held by the
 *      current instance 'this' and then copy over any resources from 'other'
 *      similar to how the copy constructor must create a full copy of all the
 *      resources and values inside the other instance being passed as a parameter
 */
Employee& Employee::operator=(const Employee& other) {
	Id = other.Id;
	Name = other.Name;
	Salary = other.Salary;
    return *this;
}

