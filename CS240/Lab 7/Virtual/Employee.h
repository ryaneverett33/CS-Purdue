#ifndef EMPLOYEE_H
#define EMPLOYEE_H

#include <iostream>
#include <algorithm>
#include <vector>
#include <stdio.h>

class Employee {
public:
	Employee(int id, char* name, double salary);
    Employee(const Employee& other);
	virtual ~Employee();

    Employee& operator=(const Employee&);

	virtual void print() = 0;
	virtual double valueOf() = 0;

    bool operator<(const Employee& rhs) const {
        return Id < rhs.Id;
    }

    bool operator>(const Employee& rhs) const {
        return Id > rhs.Id;
    }

    bool operator==(const Employee& rhs) const {
        return Id == rhs.Id;   
    }
	bool operator==(Employee& rhs) const {
        return Id == rhs.Id;   
	}

    bool operator!=(const Employee& rhs) const {
        return !(*this == rhs);
    }

    bool operator<=(const Employee& rhs) const {
        return !(*this > rhs);
    }

    bool operator>=(const Employee& rhs) const {
        return !(*this < rhs);
    }

    int getId() const {
        return Id;
    }

    const char* getName() const {
        return Name;
    }

    double getSalary() const {
        return Salary;
    }
   
protected:
	int Id;
	char* Name;
	double Salary;
};

#endif
