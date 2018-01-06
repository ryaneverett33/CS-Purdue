#include "MyVector.h"
#include "MyException.h"
#include <stdio.h>

/*******************************************************
 * For the detailed Task description, go to MyVector.h *
 *******************************************************/
/*********** Implement your functions here *************/

	
MyVector operator * (MyVector const &vec, MyVector const &vec2) {
	//puts("called MyVector, MyVector");
	if (vec.vector_size != vec2.vector_size) {
		//printf("vec: %d, vec2: %d\n", (int)vec.vector_size, (int)vec2.vector_size);
		throw MyException();
	}
	MyVector newer(vec);
	for (int i = 0; i < (int)vec.vector_size; i++) {
		newer.data[i] = (vec.data[i] * vec2.data[i]);
	}
	return newer;
}
	
MyVector operator * (int num, MyVector const &vec) {
	//puts("called MyVector, int operator");
	MyVector newer(vec.vector_size,vec.data);
	//MyVector mult(vec);
	for (int i = 0; i < (int)vec.vector_size; i++) {
		newer.data[i] = (vec.data[i] * num);
		//printf("newer[i] = %d\n", newer.data[i]);
	}
	return newer;
}

MyVector MyVector::operator = (MyVector const &vec) {
		if (this == &vec) {
			//cout << "same" << endl;
			return *this;
		}
		//cout << "not same" << endl;
		try {
			//cout << "vec vector_size: " << (int)vec.vector_size << endl;
			delete [] data;
			data = new int[vec.vector_size];
			for (int i = 0; i < (int)vec.vector_size; i++) {
				data[i] = vec.data[i];
			}
			vector_size = vec.vector_size;
		}
		catch (exception e) {
			//cout << e.what() << endl;
		}
		return *this;
	}