//
// CS252: MyMalloc Project
//
// The current implementation gets memory from the OS
// every time memory is requested and never frees memory.
//
// You will implement the allocator as indicated in the handout.
// 
// Also you will need to add the necessary locking mechanisms to
// support multi-threaded programs.
//
#define DEBUG 0
#define FRDBG 0

#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <unistd.h>
#include <sys/mman.h>
#include <pthread.h>
#include <errno.h>
#include <stdbool.h>
#include "MyMalloc.h"

#define ALLOCATED 1
#define NOT_ALLOCATED 0
#define ARENA_SIZE 2097152

pthread_mutex_t mutex;

static bool verbose = false;

extern void atExitHandlerInC()
{
  if (verbose)
    print();
}

static void * getMemoryFromOS(size_t size)
{
  // Use sbrk() to get memory from OS
  _heapSize += size;
 
  void *mem = sbrk(size);

  if(!_initialized){
      _memStart = mem;
  }

  return mem;
}


/*
 * @brief retrieves a new 2MB chunk of memory from the OS
 * and adds "dummy" boundary tags
 * @param size of the request
 * @return a FreeObject pointer to the beginning of the chunk
 */
static FreeObject * getNewChunk(size_t size)
{
  void *mem = getMemoryFromOS(size);

  // establish fence posts
  BoundaryTag *fencePostHead = (BoundaryTag *)mem;
  setAllocated(fencePostHead, ALLOCATED);
  setSize(fencePostHead, 0);
  
  if (DEBUG) fprintf(stderr, "\tTop post at %p\n", (void*)fencePostHead);

  char *temp = (char *)mem + size - sizeof(BoundaryTag);
  BoundaryTag *fencePostFoot = (BoundaryTag *)temp;
  setAllocated(fencePostFoot, ALLOCATED);
  setSize(fencePostFoot, 0);
  
  if (DEBUG) fprintf(stderr, "\tBottom post at %p\n", (void*)fencePostFoot);
 
  return (FreeObject *)((char *)mem + sizeof(BoundaryTag));
}

/**
 * @brief If no blocks have been allocated, get more memory and 
 * set up the free list
 */
static void initialize()
{
  verbose = true;

  pthread_mutex_init(&mutex, NULL);

  // print statistics at exit
  atexit(atExitHandlerInC);

  FreeObject *firstChunk = getNewChunk(ARENA_SIZE);
	if (DEBUG) fprintf(stderr, "\tFirst Chunk at %p\n", (void*)firstChunk);
  
  // initialize the list to point to the firstChunk
  _freeList = &_freeListSentinel;
  setSize(&firstChunk->boundary_tag, ARENA_SIZE - (2*sizeof(BoundaryTag))); // ~2MB
  firstChunk->boundary_tag._leftObjectSize = 0;
  setAllocated(&firstChunk->boundary_tag, NOT_ALLOCATED);

  // link list pointer hookups
  firstChunk->free_list_node._next = _freeList;
  firstChunk->free_list_node._prev = _freeList;
  _freeList->free_list_node._prev = firstChunk;
  _freeList->free_list_node._next = firstChunk;

  _initialized = 1;
}

/**
 * @brief TODO: PART 1
 * This function should perform allocation to the program appropriately,
 * giving pieces of memory that large enough to satisfy the request. 
 * Currently, it just sbrk's memory every time.
 *
 * @param size size of the request
 *
 * @return pointer to the first usable byte in memory for the requesting
 * program
 */
static void * allocateObject(size_t size)
{
  if (size == 0) {
	  return NULL;
  }
  // Make sure that allocator is initialized
  if (!_initialized)
    initialize();

	if (DEBUG) fprintf(stderr, "\tRequested size: %d\n", (int)size);
  if (size % 8 != 0) {
	  size = size + 8 - (size % 8);
	  if (DEBUG) fprintf(stderr, "\tSize is not alligned, adding: %d\n", (int)(size + 8 - (size % 8)));
  }
  //Add size of BoundaryTag
  size += sizeof(struct BoundaryTag);
  //Don't use until freeing
  //size += sizeof(FreeListNode);
  if (size < 32) size = 32;
  
  if (size > ARENA_SIZE - (3 * sizeof(BoundaryTag))) {
	  errno = ENOMEM;
	  return NULL;
  }
  
	if (DEBUG) fprintf(stderr, "\tCreating with size: %d\n", (int)size);
  
  FreeObject *currObj = _freeList->free_list_node._next;
  FreeObject *toUse = NULL;
  //FreeObject *ptr = _freeList->free_list_node._next;
  //fprintf(stderr, "Free List at %p\n", (void*)_freeList);
  while (currObj != _freeList) {
	  //get free list next for now
	  //check for enough space
	  //fprintf(stderr, "Curr Obj at: %p\n", (void*)currObj);
	  size_t freeSpace = getSize(&currObj->boundary_tag);
	  if (currObj->free_list_node._next != _freeList) {
		  //int debug = 5;
	  }
	  //fprintf(stderr, "freeSpace: %d\n", (int)freeSpace);
	  if (freeSpace > size) {
		  //use this chunk
		  toUse = currObj;
		  break;
	  }
	  //fprintf(stderr, "CurrObj doesn't have enough space with %d\n", (int)freeSpace);
	  //move on
	  currObj = currObj->free_list_node._next;
  }
  if (toUse == NULL) {
	  //Regular create new object
	  //fprintf(stderr, "Creating new FreeList Object\n");
	  //request new chunk
	  fprintf(stderr, "\tCreating new chunk\n");

    currObj = _freeList->free_list_node._next;

	  FreeObject * newObj = getNewChunk(ARENA_SIZE);
	   //initialize newObj basically initialize()
	   setSize(&newObj->boundary_tag, ARENA_SIZE - (2*sizeof(BoundaryTag)));
	   newObj->boundary_tag._leftObjectSize = 0;
	   setAllocated(&newObj->boundary_tag, NOT_ALLOCATED);
	   
     newObj->free_list_node._next = currObj;
     newObj->free_list_node._prev = _freeList;
     currObj->free_list_node._prev = newObj;
     _freeList->free_list_node._next = newObj;
	   
	   //Set our current pointer to the new chunk
	   toUse = newObj;
	   
	   //fprintf(stderr, "Added a new chunk at %p with size %d\n", (void*)newObj, getSize(&currObj->boundary_tag));
  }
  
  if (toUse == _freeList) {
	//if we're using the sentinel node
	  if (DEBUG) {
		fprintf(stderr, "toUse is at sentinel. c: %p, s:%p\n", (void*)toUse, (void*)_freeList);
	  }
  }
  
  if (DEBUG) fprintf(stderr, "\tUsing FreeObject at: %p\n", (void*)toUse);
  
  //TODO check for enough space
  size_t space = getSize(&toUse->boundary_tag);
  
  //size of Free Object (Boundary Tag) - fixed requested size
  setSize(&toUse->boundary_tag, space - size);
  
  if (DEBUG) fprintf(stderr, "\t FreeObject had a size of %d, now has %d\n", (int)space, (int)getSize(&toUse->boundary_tag));
  if (getSize(&toUse->boundary_tag) < 0) {
	  fprintf(stderr, "free object is negative in space: %d\n",
	  (int)getSize(&toUse->boundary_tag));
  }
  
  //size_t add = sizeof(FreeObject)
  size_t locAdd = space - size;
  
  //Check if there's enough space (32) in the current free obj, if there's not return the remainder of the chunk
  //fprintf(stderr, "Using space of %d and size: %d\n", (int)space, (int)size);
	FreeObject* newObj;
	if (space - size < 32){
		size += (space - size);
		setSize(&toUse->boundary_tag, 0);
		locAdd += sizeof(BoundaryTag);
		
		//create new object because this is full
		newObj = getNewChunk(ARENA_SIZE);
		setSize(&newObj->boundary_tag, ARENA_SIZE - 2 * sizeof(BoundaryTag));
		newObj->boundary_tag._leftObjectSize = 0;
		setAllocated(&newObj->boundary_tag, NOT_ALLOCATED);
		
		newObj->free_list_node._next = _freeList;
		newObj->free_list_node._prev = toUse->free_list_node._prev;
		
		_freeList->free_list_node._next = newObj;
		//_freeList->free_list_node._prev = newObj;
	}
	char* newSpot = (char*)toUse + locAdd;
	BoundaryTag* tag = (BoundaryTag*)newSpot;
	tag->_leftObjectSize = (int)getSize(&toUse->boundary_tag);
  setSize(tag, size);
  
  //Set left object size (our new size) of the f object
  if (space < ARENA_SIZE - 3 * sizeof(BoundaryTag)) {
	  char* rightLocation = (char*)toUse + space;
		BoundaryTag* rightTag = (BoundaryTag*)rightLocation;
		//fprintf(stderr, "Got Right location at %p with size: %d\n", (void*)rightLocation, getSize(rightTag));
		rightTag->_leftObjectSize = size;
  }
  
  //tag->_leftObjectSize = space - size;
  setAllocated(tag, ALLOCATED);
	if (DEBUG) fprintf(stderr, "\tCreated Object at %p with size %d and boudary tag at %p\n", (void*)newSpot, (int)getSize(tag), (void*)tag);
  
  /*if (space - size < 32) {
	  _freeList->free_list_node._next = newObj;
	  _freeList->free_list_node._prev = newObj;
  }*/
  
  
  pthread_mutex_unlock(&mutex);
  //return getMemoryFromOS(size);
  
  return (void*)newSpot + sizeof(BoundaryTag);
  //puts("Retuning from allocate()");
	//return (void*)obj + size;
}

/**
 * @brief TODO: PART 2
 * This funtion takes a pointer to memory returned by the program, and
 * appropriately reinserts it back into the free list.
 * You will have to manage all coalescing as needed
 *
 * @param ptr
 */	
static void freeObject(void *ptr)
{
	//TODO check if object is at far left or at far right, or the only object allocated
	if (FRDBG) {
		FreeObject* objPtr = _freeList;
		//fprintf(stderr, "%p [n:%p, p:%p]\n", (void*)objPtr, (void*)objPtr->free_list_node._next, (void*)objPtr->free_list_node._prev);
		objPtr = objPtr->free_list_node._next;
		while (objPtr != _freeList) {
			//fprintf(stderr, "%p [n:%p, p:%p]\n", (void*)objPtr, (void*)objPtr->free_list_node._next, (void*)objPtr->free_list_node._prev);
			objPtr = objPtr->free_list_node._next;
		}
	}
	
	if (ptr == NULL) {
		return;
	}
	
	if (FRDBG) fprintf(stderr, "\tRequested free of object at %p\n", ptr);
	//get left and right first
	char* locPtr = (char*)ptr;
	BoundaryTag* leftTag, *rightTag, *ptrTag;
	ptrTag = (BoundaryTag*)(locPtr - sizeof(BoundaryTag));
	size_t ptrSize = getSize(ptrTag);
	size_t leftSize = ptrTag->_leftObjectSize;
	
	rightTag = (BoundaryTag*)(locPtr + ptrSize - sizeof(BoundaryTag));
	leftTag = (BoundaryTag*)(locPtr - leftSize - sizeof (BoundaryTag));
	if (FRDBG) fprintf(stderr, "\trightTag at: %p with size: %d and alloc %d\n", (void*)rightTag, (int)getSize(rightTag), (int)isAllocated(rightTag));
	if (FRDBG) fprintf(stderr, "\tleftTag at: %p with size: %d and alloc %d\n", (void*)leftTag, (int)getSize(leftTag), (int)isAllocated(leftTag));
	
	bool leftAlloc = false, rightAlloc = false;
	//check left first
	if (isAllocated(leftTag)) {
		leftAlloc = true;
	}
	//then check right
	if (isAllocated(rightTag)) {
		rightAlloc = true;
	}
	if (leftAlloc && rightAlloc) {
		if (FRDBG) {}
		//fprintf(stderr, "\tno coalesc\n");
		//can't coalesc, add to free list
		FreeObject* newObj = (FreeObject*)ptrTag;
		setAllocated(&newObj->boundary_tag, NOT_ALLOCATED);
		newObj->boundary_tag._leftObjectSize = leftSize;
		newObj->free_list_node._next = _freeList->free_list_node._next;
		newObj->free_list_node._prev = _freeList;
		_freeList->free_list_node._next->free_list_node._prev = newObj;
		_freeList->free_list_node._next = newObj;
	}
	else if (!leftAlloc && rightAlloc) {
		if (FRDBG) {}
		//fprintf(stderr, "\tCoalesc left side\n");
		//coalesc the left side
		//left side is already a free obj
		FreeObject* leftObj = (FreeObject*)leftTag;
		setSize(&leftObj->boundary_tag, leftSize + ptrSize);
		setAllocated(&leftObj->boundary_tag, NOT_ALLOCATED);
	}
	else if (!leftAlloc && !rightAlloc) {
		//coalesc both sides
		if (FRDBG) {}
		//fprintf(stderr, "\tCoalesc both sides\n");
		FreeObject* leftObj = (FreeObject*)leftTag;
		FreeObject* rightObj = (FreeObject*)rightTag;
		size_t rightSize = getSize(rightTag);
		setSize(leftTag, leftSize + ptrSize + rightSize);
		setAllocated(leftTag, NOT_ALLOCATED);
		
		//remove rightObj from freeList
		FreeObject* searchObj = _freeList->free_list_node._next;
		while (searchObj != _freeList) {
			//https://en.wikipedia.org/wiki/Doubly_linked_list#Removing_a_node
			if (searchObj == rightObj) {
				if (FRDBG) fprintf(stderr, "Found! search: %p, rightObj: %p\n", (void*)searchObj, (void*)rightObj);
				/*if (searchObj->free_list_node._prev == _freeList) {
					//first element
					//_freeList->free_list_node._next = rightObj->free_list_node._next;
				}
				else {
					//searchObj->free_list_node._prev->free_list_node._next = rightObj->free_list_node._next;
				}
				if (searchObj->free_list_node._next == _freeList) {
					//last element
					//searchObj->free_list_node._prev->free_list_node._next = _freeList;
				}
				else {
					//searchObj->free_list_node._next->free_list_node._prev = searchObj->free_list_node._prev;
				}*/
				//searchObj->free_list_node._next
				leftObj->free_list_node._next = searchObj->free_list_node._next;
				if (searchObj->free_list_node._prev == _freeList) {
					if (FRDBG) fprintf(stderr, "prev is freeList\n");
				}
				//leftObj->free_list_node._next->free_list_node._next = searchObj->free_list_node._prev;
				searchObj->free_list_node._next->free_list_node._prev = leftObj;
				if (searchObj->free_list_node._next == _freeList) {
					if (FRDBG) fprintf(stderr, "next is freeList\n");
				}
				break;
			}
			searchObj = searchObj->free_list_node._next;
		}
	}
	else if (!rightAlloc && leftAlloc) {
		if (FRDBG) {}
		//fprintf (stderr, "\tCoalesc the right side\n");
		//coalesc the right side
		//right side is already a free obj
		//original object in list needs to be removed and updated to the new position (move left)
		size_t rightSize = getSize(rightTag);
		FreeObject* rightObj = (FreeObject*)rightTag;
		FreeObject* newObj = (FreeObject*)ptrTag;
		setSize(&newObj->boundary_tag, ptrSize + rightSize);
		//setSize(&newObj->boundary_tag, 21);
		setAllocated(&newObj->boundary_tag, NOT_ALLOCATED);
		
		//find rightObj in list
		FreeObject* searchObj = _freeList->free_list_node._next;
		while (searchObj != _freeList) {
			if (searchObj == rightObj) {
				if (FRDBG) fprintf(stderr, "free search found rightObj in list\n");
				break;
			}
			//progress searchObj
			searchObj = searchObj->free_list_node._next;
		}
		if (searchObj != rightObj) {
			if (FRDBG) fprintf(stderr, "free search COULDN'T find rightObj in list\n");
			return;
		}
		//update newObj, prev, and next if (referenced)
		newObj->free_list_node._next = searchObj->free_list_node._next;
		newObj->free_list_node._prev = searchObj->free_list_node._prev;
		
		FreeObject* prevObj = newObj->free_list_node._prev;
		FreeObject* nextObj = newObj->free_list_node._next;
		
		//check prev
		if (FRDBG) fprintf(stderr, "prev._next: %p, prev._prev: %p, search: %p, rightObj: %p\n", (void*)prevObj->free_list_node._next, (void*)prevObj->free_list_node._prev, (void*)searchObj, (void*)rightObj);
		if (prevObj->free_list_node._next == searchObj) {
			if (FRDBG) fprintf(stderr, "prevObj._next == newObj\n");
			if (FRDBG) prevObj->free_list_node._next = newObj;
		}
		if (prevObj->free_list_node._prev == searchObj) {
			if (FRDBG) fprintf(stderr, "prevObj._prev = newObj\n");
			prevObj->free_list_node._prev = newObj;
		}
		/*else if (prevObj == _freeList) {
			_freeList->free_list_node._next = newObj;
		}*/
		//check next
		if (FRDBG) fprintf(stderr, "next._next: %p, next._prev: %p, search: %p, rightObj: %p\n", (void*)nextObj->free_list_node._next, (void*)nextObj->free_list_node._prev, (void*)searchObj, (void*)rightObj);
		if (nextObj->free_list_node._prev == searchObj) {
			if (FRDBG) fprintf(stderr, "nextObj._prev = newObj\n");
			nextObj->free_list_node._prev = newObj;
		}
		if (nextObj->free_list_node._next == searchObj) {
			if (FRDBG) fprintf(stderr, "nextObj._next = newObj\n");
			nextObj->free_list_node._next = newObj;
		}
		if (_freeList->free_list_node._next == searchObj) {
			if (FRDBG) fprintf(stderr, "freeList._next = newObj\n");
			_freeList->free_list_node._next = newObj;
		}
		if (_freeList->free_list_node._prev == searchObj) {
			if (FRDBG) fprintf(stderr, "freeList._prev = newObj\n");
			_freeList->free_list_node._prev = newObj;
		}
		if (FRDBG) fprintf(stderr, "free._next: %p, free._prev: %p, search: %p, rightObj: %p\n", (void*)_freeList->free_list_node._next, (void*)_freeList->free_list_node._prev, (void*)searchObj, (void*)rightObj);
		
	}
	
	
	
  return;
}

void print()
{
  printf("\n-------------------\n");

  printf("HeapSize:\t%zd bytes\n", _heapSize);
  printf("# mallocs:\t%d\n", _mallocCalls);
  printf("# reallocs:\t%d\n", _reallocCalls);
  printf("# callocs:\t%d\n", _callocCalls);
  printf("# frees:\t%d\n", _freeCalls);

  printf("\n-------------------\n");
}

void print_list()
{
    printf("FreeList: ");
    if (!_initialized) 
        initialize();
    FreeObject *ptr = _freeList->free_list_node._next;
    while (ptr != _freeList) {
        long offset = (long)ptr - (long)_memStart;
        printf("[offset:%ld,size:%zd]", offset, getSize(&ptr->boundary_tag));
        ptr = ptr->free_list_node._next;
        if (ptr != NULL)
            printf("->");
    }
    printf("\n");
}

void increaseMallocCalls() { _mallocCalls++; }

void increaseReallocCalls() { _reallocCalls++; }

void increaseCallocCalls() { _callocCalls++; }

void increaseFreeCalls() { _freeCalls++; }

//
// C interface
//

extern void * malloc(size_t size)
{
  pthread_mutex_lock(&mutex);
  increaseMallocCalls();
  
  return allocateObject(size);
}

extern void free(void *ptr)
{
  pthread_mutex_lock(&mutex);
  increaseFreeCalls();
  
  if (ptr == 0) {
    // No object to free
    pthread_mutex_unlock(&mutex);
    return;
  }
  
  freeObject(ptr);
}

extern void * realloc(void *ptr, size_t size)
{
  pthread_mutex_lock(&mutex);
  increaseReallocCalls();

  // Allocate new object
  void *newptr = allocateObject(size);

  // Copy old object only if ptr != 0
  if (ptr != 0) {

    // copy only the minimum number of bytes
    FreeObject *o = (FreeObject *)((char *) ptr - sizeof(BoundaryTag));
    size_t sizeToCopy = getSize(&o->boundary_tag);
    if (sizeToCopy > size) {
      sizeToCopy = size;
    }

    memcpy(newptr, ptr, sizeToCopy);

    //Free old object
    freeObject(ptr);
  }

  return newptr;
}

extern void * calloc(size_t nelem, size_t elsize)
{
  pthread_mutex_lock(&mutex);
  increaseCallocCalls();
    
  // calloc allocates and initializes
  size_t size = nelem * elsize;

  void *ptr = allocateObject(size);

  if (ptr) {
    // No error
    // Initialize chunk with 0s
    memset(ptr, 0, size);
  }

  return ptr;
}

