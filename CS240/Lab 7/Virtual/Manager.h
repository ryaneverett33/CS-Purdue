#ifndef MANAGER_H
#define MANAGER_H

#include <iostream>
#include <algorithm>
#include <vector>

#include "../arraylist-src/ArrayList.h"
#include "Employee.h"
#include "Engineer.h"

class Manager: public Employee
{
public:
	Manager(int id, char* name, double salary);
    Manager(const Manager& other);
	~Manager();
    Manager& operator=(const Manager& other);

	bool addEngineerToManage(const Engineer& engineer);
	bool stopManagingEngineer(const Engineer& engineer);

	void print();
	double valueOf();

protected:
	ArrayList<Engineer*> *Engineers;
};

#endif
