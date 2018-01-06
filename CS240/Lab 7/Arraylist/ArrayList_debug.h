#ifndef ARRAYLIST_H
#define ARRAYLIST_H

#include <algorithm>
#include <exception>
#include <iostream>
#include <type_traits>
#include <stdlib.h>
#include <string.h>

#define debug 1

/**
 * TODO, implement the ArrayList here in this header file.
 *
 * Why implement in the header file:
 *      C++ implements template classes inside of header files,
 *      which are then #included into the files where they are actually
 *      used. When the template is used, a concrete type is passed in
 *      and replaces T everywhere T appears (this is called template instantiation).
 *      So for example, 'ArrayList<int> a;' instantiates the template with T as
 *      an 'int', creating an new class with T replaced with int. The implementation
 *      of the template must be in the .h file because the compiler does not
 *      know ahead of time which types will replace T, so the compiler must
 *      always have access to the full implementation of the template class
 *      any location where the template could be instantiated. The easiest way
 *      to do this is to implement the template in a header file and simple include
 *      the header file in any file where the template is used.
 */

/**
 * ArrayList class
 *
 * This class implements an ArrayList in a fashion
 * that is similar to that of Java, but also adds
 * a lot of useful C++ features.
 */
template<class T>
class ArrayList
{
public:
    ArrayList();
    ArrayList(const ArrayList<T>& other);
    ~ArrayList();
    
    int indexOf(const T& item);
    int indexOf(const T& item, int occurrence);
    int lastIndexOf(const T& item);
    
    int size() const;
    T& get(int index);
    T& operator[](int index);
    const T& operator[](int index) const;

    const T remove(int index);
    void remove(const T& item, bool* ok);
    
    void add(const T& item);
    void add(const T& item, int index);
    
    void push_back(const T& item);
    void push_front(const T& item);

    void clear();

    bool isEmpty();
    bool contains(const T& item);

    void sort();
    
    ArrayList<T>& operator=(const ArrayList<T>& other);
    bool operator==(const ArrayList<T>& other);

    ArrayList<T>& operator<<(const T& item);
    ArrayList<T>& operator<<(const ArrayList<T>& other);

    ArrayList<T>& operator+=(const T& item);
    ArrayList<T>& operator+=(const ArrayList<T>& other);

private:
    T * pElements;
    int m_size;
    int m_capacity;
    const static int SIZE_INCREMENT = 2;
};


/**
 * Default Constructor. 
 * Remarks:
 *      The constructor is called when a new instance is
 *      allocated (either on the stack automatically or
 *      on the heap via 'new') and must allocate and initialize
 *      and memory or other resources needed
 */
template<class T>
ArrayList<T>::ArrayList() :
    m_size(0),
    m_capacity(SIZE_INCREMENT) {
    pElements = new T[SIZE_INCREMENT];
}

/**
 * Copy constructor, to make a new instance as a copy of another
 * Parameters:
 *      other - Constant reference to another ArrayList<T> instance that we are copying
 * Remarks:
 *      The copy constructor is called to create a new instance as a copy
 *      of an existing instance. Copies should be 'deep' meaning that any
 *      underlying resources such as memory should also be copied over.
 */
template<class T>
ArrayList<T>::ArrayList(const ArrayList<T>& other) {
    int otherSize = other.size();
	if (otherSize % 2 != 0) {
		if (debug) printf("copyConstructor with size: %d, setting capacity to %d\n", otherSize, otherSize + 1);
		m_capacity = otherSize + 1;
	}
	else m_capacity = otherSize;
	pElements = new T[m_capacity];
	for (int i = 0; i < otherSize; i++) {
		pElements[i] = other[i];
	}
}

/**
 * Destructor for ArrayList
 * Remarks:
 *      The destructor is called when an instance of the class is deleted,
 *      either by calling 'delete' on a pointer or when a local copy on the
 *      stack is deleted when a function returns. The destructor must cleanup
 *      any memory or resources held by the object.
 */
template<class T>
ArrayList<T>::~ArrayList() {
    /**
     * @todo Deallocate any memory or resources used in ArrayList
     */
	 m_size = 0;
	 m_capacity = 0;
	 delete [] pElements;
}

/**
 * Clear the ArrayList
 * Remarks:
 *      Clear all existing elements from the ArrayList and reset it back to its
 *      default state
 */
template<class T>
void ArrayList<T>::clear() {
    /** @todo Clear the list and shrink the array. **/ 
	//
	T *oldPointer = pElements;
	pElements = new T[SIZE_INCREMENT];
	m_capacity = SIZE_INCREMENT;
	m_size = 0;
	delete [] oldPointer;
}

/**
 * Adds an item to the ArrayList<T>
 * Parameters:
 *      item - The item to be added
 * Remarks:
 *      Add item to the end of the array,
 *      allocating resources if adding another
 *      element exceeds current capacity.
 *      You *must* use "new T[]" not realloc()
 */
template<class T>
void ArrayList<T>::add(const T& item) {
	if (m_size < m_capacity) {
		pElements[m_size] = item;
		m_size++;
	}
	else {
		//resize and then add
		T *newElements = new T[m_capacity + SIZE_INCREMENT];
		for (int i = 0; i < m_capacity; i++) {
			newElements[i] = pElements[i];
		}
		newElements[m_capacity] = item;
		T *oldPointer = pElements;
		pElements = newElements;
		delete [] oldPointer;
		//assign new meta values
		m_capacity = m_capacity + SIZE_INCREMENT;
		m_size++;
	}
}

/**
 * Adds an item at a specific index, overwriting anything at that index
 * Parameters:
 *      item - The item to add
 *      index - Where it is to be added.
 * Remarks:
 *      Add item to the array at the specified index, reallocating if needed
 *      If the index is out of bounds, throw an exception with 'throw std::exception()'
 */
template<class T>
void ArrayList<T>::add(const T& item, int index) {
	//set the element at pElements[index] to item, do not resize, do not shift
	if (index < 0) {
		if (debug) printf("add() threw exception with index=%d\n", index);
		throw std::exception();
	}
	if (index >= m_capacity) {
		if (debug) printf("add() threw exception with index:%d when capacity:%d\n", index, m_capacity);
		throw std::exception();
	}
	if (index < m_capacity) {
		//add normally
		pElements[index] = item;
	}
}

/**
 * Pushes an item at the back of the list.
 * Parameters:
 *      item - The item to push back.
 * Remarks:
 *      The item should be added immediately after the current last
 *      element in the ArrayList<T>, so you may need to expand
 *      the ArrayList<T> if it is full
 */
template<class T>
void ArrayList<T>::push_back(const T& item) {
	add(item);
}

/**
 * Push an item to the front of the list.
 * Parameters:
 *      item - The item to be pushed to the front of the list.
 * Remarks:
 *      When pushing the item to the front of the
 *      list, you must shift all other items down
 *      to make room and reallocate if more room
 *      is needed
 */
template<class T>
void ArrayList<T>::push_front(const T& item) {
	T *newElements;
	//move elements and add
	if ((m_size + 1) >= m_capacity) {
		int newCapacity = m_capacity;
		do {
			newCapacity = newCapacity + SIZE_INCREMENT;
		}
		while (newCapacity < m_capacity);
		if (debug) printf("overflow_addFront, newCapacity: %d\n", newCapacity);
		newElements = new T[newCapacity];
		for (int i = 0; i < newCapacity; i++) {
			if (i == 0) {
				newElements[i] = item;
				continue;
			}
			else {
				newElements[i] = pElements[i-1];
			}
		}
		T *oldPointer = pElements;
		pElements = newElements;
		delete [] oldPointer;
		m_size++;
		m_capacity = newCapacity;
	}
	else {
		printf("capacity: %d, size: %d\n", m_capacity, m_size);
		newElements = new T[m_capacity];
		for (int i = 0; i < m_capacity; i++) {
			if (i == 0) {
				newElements[i] = item;
			}
			else {
				newElements[i] = pElements[i-1];
			}
		}
		T *oldPointer = pElements;
		pElements = newElements;
		delete [] oldPointer;
		m_size++;
	}
}

/**
 * Remove the item at a specific index.
 * Parameters:
 *      index - Index of the thing to be removed.
 * Returns:
 *      Shallow copy of the item we removed.
 * Remarks:
 *      All other items should be shifted over to fill in the vacated index      
 */
template<class T>
const T ArrayList<T>::remove(int index) {
    const T myT = T();
    /**
     * @todo Remove the item in the index-th
     * index and return it.
     */
	 //
	if (index < 0 || index >= m_capacity) {
		if (debug) printf("remove() at index=%d is invalid\n",index);
		if (debug) printf("remove(): capacity: %d, index:%d\n", m_capacity, index);
		return myT;
	}
	T actualT = pElements[index];
	bool indexSet = false;
	for (int i = 0; i < m_capacity; i++) {
		if (i == index) indexSet = true;
		if (indexSet) {
			if (i == (m_capacity - 1)) break;
			pElements[i] = pElements[i+1];
		}
		else continue;
	}
	m_size--;
    return actualT;
}

/**
 * Removes a particular item from the list.
 * Parameters:
 *      item - Item to remove from the ArrayList, shifting the elements to fill the gap.
 *      ok - Set to true upon successful removal. Do nothing with this parameter if NULL.
 * Remarks:
 *      If the ok parameter is NULL, proceed as normal, except you will not store
 *      the outcome of the operation (true, or false) in the location the pointer
 *      is pointing to (it's an optional parameter)
 */
template<class T>
void ArrayList<T>::remove(const T & item, bool * ok) {
    /**
     * @todo Find and remove item within the array.
     *  Upon successful removal, set ok to true unless ok is NULL
     */
	 //
	 for (int i = 0; i < m_capacity; i++) {
		if (pElements[i] == item) {
			if (remove(i) == (const T)item) {
				if (debug) puts("remove(const,bool) completed successfully");
				if (ok != NULL) *ok = true;
			}
			else {
				if (debug) puts("remove(const,bool) found item but remove() failed to return proper");
			}
		}
	}
}

/**
 * Check if the list is empty or not
 * Returns:
 *      True if the list is empty, false if not
 */
template<class T>
bool ArrayList<T>::isEmpty() {
    return m_size == 0;
}

/**
 * Check if an item is in the ArrayList.
 * Parameters:
 *      item - The item we want to search for.
 * Returns:
 *      Returns true if 'item' is in the ArrayList<T>, false otherwise
 */
template<class T>
bool ArrayList<T>::contains(const T& item) {
    /**
     * @todo Return true if object is in the list.
     */
	 //
	for (int i = 0; i < m_size; i++) {
		if (pElements[i] == item) return true;
	}
    return false;
}

/**
 * Returns the first index of an item in the ArrayList
 * Parameters:
 *      item - Item to search for the first index at which it occurs (first starting at 0)
 * Returns:
 *      The first index of 'item' or -1 if it doesn't exist in the ArrayList<T>
 */
template<class T>
int ArrayList<T>::indexOf(const T& item) {
    /**
     * @todo Find the index of item in the ArrayList<T>,
     * or return -1 if not found.
     */
	 //
	for (int i = 0; i < m_size; i++) {
		if (pElements[i] == item) return i;
	}
    return -1;
}

/**
 * Return the index of the ith occurence of item.
 * Parameters:
 *      item - Item to search for
 *      i - Which occurence of item to search for (1st, 2nd, etc).
 * Returns:
 *      The index of the ith occurence, -1 if an ith occurence doesn't exist, or if i <= 0
 */
template<class T>
int ArrayList<T>::indexOf(const T& item, int i) {
    /**
     * @todo Return the index of the ith
     * occurrence of object.
     */
	//
	if (i <= 0) return -1;
	int occurence = 0;
	for (int j = 0; j < m_size; j++) {
		if (pElements[j] == item) {
			occurence++;
			if (occurence == i) return j;
		}
	}
    return -1;
}

/**
 * Check for the last index of an object.
 * Parameters:
 *      item - Item to search for
 * Returns:
 *      Index of the last occurence of item in the ArrayList<T> or -1
 */
template<class T>
int ArrayList<T>::lastIndexOf(const T& item) {
    /**
     * @todo Return the last index of item in the array.
     */
	 //
	int index = -1;
	for (int i = 0; i < m_size; i++) {
		if (pElements[i] == item) index = i;
	}
    return index;
}

/**
 * Get the size of the array
 * Returns:
 *      The number of elements in the ArrayList<T>
 */
template<class T>
int ArrayList<T>::size() const {
    return m_size;
}

/**
 * Get the element at a certain index
 * Parameters:
 *      index - The index from which to retrieve an element
 * Returns:
 *      A reference to the item at index
 * Remarks:
 *      If the index is out of bounds, throw an exception with 'throw std::exception()'
 */
template<class T>
T& ArrayList<T>::get(int index) {
    // TODO, error checking   
	//
	if (index < 0 || index >= m_capacity) {
		if (debug) printf("get() threw exception for index=%d\n",index);
		if (debug) printf("get()_capacity: %d, index:%d\n", m_capacity, index);
		throw std::exception();
	}
    else return pElements[index];
}

/**
 * Get the element at a certain index
 * Parameters:
 *      index - The index from which to retrieve an element
 * Returns:
 *      A reference to the item at index
 * Remarks:
 *      If the index is out of bounds, thrown an exception with 'throw std::exception();'
 */
template<class T>
T& ArrayList<T>::operator[](int index) {
    // TODO, error checking /
	//
    if (index < 0 || index >= m_capacity) {
		if (debug) printf("[] operator threw exception for index=%d\n",index);
		throw std::exception();
	}
    else return pElements[index];
}

/**
 * Get the element at a certain index
 * Parameters:
 *      index - The index from which to retrieve an element
 * Returns:
 *      A reference to the item at index
 * Remarks:
 *      If the index is out of bounds, thrown an exception with 'throw std::exception();'
 */
template<class T>
const T& ArrayList<T>::operator[](int index) const {
    // TODO, error checking /
	//
	if (index < 0 || index >= m_capacity) {
		if (debug) printf("const [] operator threw exception for index=%d\n",index);
		throw std::exception();
	}
    else return pElements[index];
}

/**
 * Copy assignment operator
 * Parameters:
 *      other - The other instance we are being assigned from
 * Returns:
 *      A reference to the current instance 'this' that was assigned to 
 * Remarks:
 *      A copy assignment operator is invoked when an assignment is occuring,
 *      for instance ArrayList<int> a = b; where b is an existing ArrayList<T>.
 *      The operator should free any resources currently being held by the current
 *      instance 'this' and then copy over any resources from 'other' similar to
 *      how the copy constructor must create a full copy of all the resources and
 *      values inside the other instance being passed as a parameter
 */
template<class T>
ArrayList<T> & ArrayList<T>::operator=(const ArrayList<T>& other) {
	~ArrayList();	//call the destructor for the global this variable
	//screw calling the copy constructor, we can do it ourselves
	int otherSize = other.size();
	if (otherSize % 2 != 0) {
		if (debug) printf("copyConstructor with size: %d, setting capacity to %d\n", otherSize, otherSize + 1);
		m_capacity = otherSize + 1;
	}
	else m_capacity = otherSize;
	pElements = new T[m_capacity];
	for (int i = 0; i < otherSize; i++) {
		pElements[i] = other[i];
	}
    return *this;
}
    
/**
 * Equals operator.
 * Parameters:
 *      other - ArrayList with which we are checking equality.
 * Returns:
 *      True, if both ArrayList<T>s are of the same length and each element in the
 *      ArrayList<T>s are equal to each other, false otherwise
 */
template<class T>
bool ArrayList<T>::operator==(const ArrayList<T> & other) {
	//
	bool sizeCheck = other.size() == m_size;
	if (!sizeCheck) return false;
	bool elementsCheck = true;
	for (int i = 0; i < m_size; i++) {
		if (pElements[i] != other[i]) elementsCheck = false;
		break;
	}
    return sizeCheck && elementsCheck;
}

/**
 * Overloads the input operator.
 * Parameters:
 *      item  - Item to add to the back of the ArrayList<T>.
 * Returns:
 *      A reference to the current ArrayList<T> so operators can be chained together
 * Remarks:
 *      The input element shall be added to the back of the array.
 */
template<class T>
ArrayList<T>& ArrayList<T>::operator<<(const T& item) {
	//
	add(item);
    return *this;
}

/**
 * Overloads the input operator. 
 * Parameters:
 *      other - The other list to adjoin, copy the elements over
 * Returns:
 *      A reference to the current ArrayList<T> so operators can be chained together
 * Remarks:
 *      The list shall be appended to end of this one and the contents of 'other'
 *      shall be copied over so that the list passed as a parameter is not modified
 */
template<class T>
ArrayList<T>& ArrayList<T>::operator<<(const ArrayList<T> & other) {
    /**
     * @todo Append another ArrayList<T> to the end of this one.
     */
	 //
	for (int i = 0; i < other.size(); i++) {
		T element = other[i];
		add(element);
	}
    return *this;
}

/**
 * Overloads the += operator.
 * Parameters:
 *      item - The item to add to the end.
 * Returns:
 *      A refernece to the current ArrayList<T> so operators can be chained together
 * Remarks:
 *      This adds another element to the list, just like <<.
 */
template<class T>
ArrayList<T>& ArrayList<T>::operator+=(const T& item) {
    /**
     * @todo This should be the same as <<
     */
	//
	add(item);
    return *this;
}

/**
 * Overloads the += operator.
 * Parameters: 
 *      other - The other list you are to append to the end of the current ArrayList<T>
 * Returns:
 *      A reference to the current ArrayList<T> so operators can be chained together
 * Remarks:
 *      Appends another ArrayList<T> to the end of the current ArrayList<T>
 */
template<class T>
ArrayList<T>& ArrayList<T>::operator+=(const ArrayList<T> & other) {
    /**
     * @todo Analogously, this does the same as <<.
     */
	 //
	for (int i = 0; i < other.size(); i++) {
		T element = other[i];
		add(element);
	}
    return *this;
}


/**
 * Sorts the given list in ascending order in place
 * Remarks:
 *      This sorts the list in ascending order. It is assumed
 *      that the < operator has been overloaded in the type T
 */
template<class T>
void ArrayList<T>::sort() {
    /**
     * @todo Sort the array in ascending order.
     */
	 //
	bool didSwitch;
	do {
		didSwitch = false;
		for (int i = 1; i < m_size; i++) {
			if (pElements[i-1] > pElements[i]) {
				T oldElement = pElements[i-1];
				pElements[i-1] = pElements[i];
				pElements[i] = oldElement;
				didSwitch = true;
			}
		}
	}
	while (didSwitch);
}

#endif
