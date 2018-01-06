#include "Manager.h"
#include "Engineer.h"
#include <stdio.h>

void createEngineer() {
	Engineer *eng = new Engineer(33, "jeff", 130.00);
	Product p;
	p.data = 52;
	p.cost = 512;
	Product p2;
	p2.data = 25478;
	p2.cost = 1000.5f;
	eng->addProduct(p);
	eng->addProduct(p2);
	eng->print();
	printf("value of engineer: %lf\n", eng->valueOf());
	puts("Remove p1");
	if (!eng->removeProduct(p)) {
		puts("failed to remove product");
	}
	else {
		eng->print();
	}
}
void createManager() {
	puts("creating Managers and Engineers");
	Manager *man = new Manager(55, "gustavo", 250.00);
	Engineer eng1(2,"jude",124);
	Engineer eng2(3, "red", 542);
	Engineer eng3(99, "gold", 7852.05f);
	puts("adding engineers");
	if (!man->addEngineerToManage(eng1)) {
		puts("Failed to add engineer1 to manager");
	}
	if (!man->addEngineerToManage(eng2)) {
		puts("Failed to add engineer2 to manager");
	}
	if (!man->addEngineerToManage(eng3)) {
		puts("Failed to add engineer3 to manager");
	}
	man->print();
	printf("Man value: %lf\n", man->valueOf());
	if (!man->stopManagingEngineer(eng1)) {
		puts("Failed to remove engineer1 to manager");
	}
	man->print();
}
int main() {
	//createEngineer();
	createManager();
	return 1;
}