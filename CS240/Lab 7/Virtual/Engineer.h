#ifndef ENGINEER_H
#define ENGINEER_H

#include <iostream>
#include <algorithm>
#include <vector>

#include "../arraylist-src/ArrayList.h"
#include "Employee.h"

struct Product{
	int data;
	float cost;
	bool operator==(const Product & other) {
	if (data == other.data || cost == other.cost) {
		std::cout << "The two products equal" << std::endl;
		return true;
	}
	else {
		std::cout << "The two products do not equal" << std::endl;
		return false;
	}
	}
	bool operator==(Product & other) {
		if (data == other.data || cost == other.cost) {
		std::cout << "The two products equal" << std::endl;
		return true;
	}
	else {
		std::cout << "The two products do not equal" << std::endl;
		return false;
	}
	}
};

class Engineer: public Employee
{
public:
	Engineer(int id, char* name, double salary);
	Engineer(const Engineer& other);

	bool addProduct(const Product& product);
	bool removeProduct(const Product& product);

	void print();
	double valueOf();
	
	bool operator==(const Engineer& rhs) const {
		std::cout << getId() << " vs " << rhs.getId() << std::endl;
        return getId() == rhs.getId();   
    }

protected:
	ArrayList<Product> *Products;
};

#endif
