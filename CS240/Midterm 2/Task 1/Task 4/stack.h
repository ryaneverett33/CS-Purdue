/* a struct that represents an item on the stack, with a double and the callback function
pointer as its payload */
struct item{
	double value;
	int (*callback)(void);
};

struct stack{
	/* the stack itself, an array of pointers to item structs */
	struct item **contents;
	/* the index of the item at the top of the stack, ­1 if empty */
	int top;
	/* the maximum size of the stack/contents array */
	int max_size;
};

struct stack * newStack(int max_size);

int push(struct stack * s, double value, int (*callback)());

double popAndCall(struct stack * s);