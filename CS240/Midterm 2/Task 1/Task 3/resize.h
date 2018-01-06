/* a struct representing an array that is resizable */
typedef struct resizableArray{
	/* the array itself, of integers */
	int * array;
	/* the current number of elements in the array */
	int currSize;
	/* the maximum number of elements in the array */
	int maxSize;
} resizableArray;

resizableArray* rArrayInitialize(int maxSize);
int rArrayAdd(resizableArray *rArray, int x);
int rArrayRemove(resizableArray *rArray, int i);