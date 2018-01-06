#include "Engineer.h"
#include "stdio.h"

/*
	To Do: Implement class Engineer
*/

double totalCost;
/**
 * Constructor
 * Parameters:
 *      id - The Employee ID of this new employee
 *      name - A pointer to a character string containing the Engineer's name
 *      salary - The Engineer's salary (This will be lower than the Manager's salary....)
 * Remarks:
 *
 */
Engineer::Engineer(int id, char* name, double salary) : Employee(id, name, salary) {
	//forwards the Engineer constructor to the Employee constructor
	ArrayList<Product> *products = new ArrayList<Product>();
	Products = products;
	totalCost = 0;
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
Engineer::Engineer(const Engineer& other) : Employee(other) {
	ArrayList<Product> *products = new ArrayList<Product>();
	Products = products;
	totalCost = 0;
	for (int i = 0; i < other.Products->size(); i++){
		Products->add(other.Products->get(i));
		totalCost = totalCost + other.Products->get(i).cost;
	}
}


/**
 * Assign a given Product to an Engineer
 * Parameter:
 *      product - The Product to be managed
 * Returns:
 *      true if the product was added successfully, false otherwise
 */
bool Engineer::addProduct(const Product& product) {
	Products->add(product);
	int index = Products->indexOf(product);
	if (index >= 0) {
		totalCost = totalCost + product.cost;
		return true;
	}
	else {
		return false;
	}
}

/**
 * Remove a given Product from the Engineer
 * Returns:
 *      true if the project was found and removed from
 *      the list of managed projects, false otherwise
 */
bool Engineer::removeProduct(const Product& product) {
	bool doesContain = Products->contains(product);
	if (doesContain) {
		bool *ok = new bool;
		Products->remove(product,ok);
		if (*ok) {
			totalCost = totalCost - product.cost;
			return true;
		}
		else {
			return false;
		}
	}
	else {
		bool *ok = new bool;
		Products->remove(product,ok);
		if (*ok) {
			totalCost = totalCost - product.cost;
			return true;
		}
		return false;
	}
}

/**
 * Print out the information about the Engineer
 * Remarks:
 *      Print out the Engineer's information in the following
 *      format 'Employee ID: %d\nName: %s\nSalary: %d' and print
 *      each product in the following format 'Has Product Data: %d Cost: %f\n'
 *
 */
void Engineer::print() {
	printf("Employee ID: %d\n", getId());
	printf("Name: %s\n", getName());
	printf("Salary: %lf\n", getSalary());
	for (int i = 0; i < Products->size(); i++) {
		Product prod = Products->get(i);
		printf("Has Product Data: %d Cost: %f\n", prod.data, prod.cost);
	}
}

/**
 * Return the value of the Engineer
 * Returns:
 *      The total cost of all the products the engineer is working on
 */
double Engineer::valueOf() {
    return totalCost;
}
