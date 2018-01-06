#include "Manager.h"
#include "string.h"
#include "stdio.h"

/*
	To Do: Implement class Manager
*/
double totalValue;
/**
 * Constructor
 * Parameters:
 *      id - The Employee ID of this Manager
 *      name - A pointer to a character string containing the name of this Manager
 *      salary - The Manager's salary
 *              (In practice, this will be a much bigger number than the Engineer's salary...)
 *  Remarks:
 *      The constructor is called when a new instance is
 *      allocated, either on the stack automatically or
 *      on the heap via 'new' and must allocate memory or
 *      other resources and initialize instance member variables
 */
Manager::Manager(int id, char* name, double salary) : Employee(id, name, salary) {
	Engineers = new ArrayList<Engineer*>();
	totalValue = 0;
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
Manager::Manager(const Manager& other) : Employee(other) {
	totalValue = 0;
	Engineers = new ArrayList<Engineer*>();
	for (int i = 0; i < other.Engineers->size(); i++){
		Engineers->add(other.Engineers->get(i));
		totalValue = totalValue + other.Engineers->get(i)->getSalary();
	}
}

/**
 * Destructor for Manager
 * Remarks:
 *      The destructor is called when an instance of the class is deleted,
 *      either by calling 'delete' on a pointer or when a local copy on the
 *      stack is deleted when a function returns. The destructor must cleanup
 *      any memory or resources held by the object.
 *
 */
Manager::~Manager() {
	totalValue = 0;
	for (int i = 0; i < Engineers->size(); i++) {
		delete Engineers->get(i);
	}
	Engineers->clear();
	delete Engineers;
}

/**
 * Copy assignment operator
 * Parameters:
 *      other - The other instance we are being assigned from
 * Returns:
 *      A reference to the current instance 'this' that was assigned to
 * Remarks:
 *      A copy assignment operator is invoked when an assignment is occuring,
 *      for instance Engineer a = b; where b is an existing Engineer instance.
 *      The operator should free any resources currently being held by the
 *      current instance 'this' and then copy over any resources from 'other'
 *      simular to how the copy constructor must create a full copy of all the
 *      resources and values inside the other instance being passed as a parameter
 */
Manager& Manager::operator=(const Manager& other) {
	ArrayList<Engineer*> *oldEngineers = Engineers;
	totalValue = 0;
	Engineers = new ArrayList<Engineer*>();
	//copy over all engineers
	for (int i = 0; i < other.Engineers->size(); i++) {
		totalValue = totalValue + other.Engineers->get(i)->getSalary();
		Engineers->add(other.Engineers->get(i));
	}
	delete oldEngineers;
    return *this;
}

/**
 * Assign a given Employee to be managed by this Manager
 * Parameter:
 *      The Employee to be managed
 * Returns:
 *      true if the employee was added successfully, false otherwise
 * Remarks:
 *      You can assume that the same Engineer with not be added multiple times
 */
bool Manager::addEngineerToManage(const Engineer& engineer) {
	//Engineer::Engineer(int id, char* name, double salary) : Employee(id, name, salary) {
	Engineer *eng = new Engineer(engineer);
	Engineers->add(eng);
	if (Engineers->contains(eng)) {
		totalValue = totalValue + eng->getSalary();
		//puts("does contain");
		return true;
	}
    else {
    	puts("does not contain");
		return false;
	}
}

/**
 * Stop managing an engineer, and remove from the list
 * Returns:
 *      true if the employee was found and removed from
 *      the list of managed employees, false otherwise
 */
bool Manager::stopManagingEngineer(const Engineer& engineer) {
	Engineer *eng = new Engineer(engineer);
	bool doesContain = Engineers->contains(eng);
    if (doesContain) {
		bool *ok = new bool;
		Engineers->remove(eng,ok);
		if (*ok) {
			totalValue = totalValue - eng->getSalary();
			return true;
		}
		else {
			*ok = false;
			return false;
		}
	}
	else {
		return false;
	}
}

/**
 * Print out the Manager to standard output
 * Remarks:
 *      The format of the output should be 'Employee ID: %d\nName: %s\nSalary: %d\n'
 *      For each employee managed by the Manager, you should also print
 *      out 'Has Employee %d\n' repeated for each employee
 */
void Manager::print() {
	printf("Employee ID: %d\n", getId());
	printf("Name: %s\n", getName());
	printf("Salary: %lf\n", getSalary());
	for (int i = 0; i < Engineers->size(); i++) {
		printf("Has Employee %d\n", Engineers->get(i)->getId());
	}
}

/**
 * Return the value of the Manager
 * Returns:
 *      The value of the sum of the salaries of all employees managed
 *      by this particular manager
 */
double Manager::valueOf() {
    return totalValue;
}
