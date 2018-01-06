/* a struct representing an item in the queue, with an integer as payload */
typedef struct item {
	int value;
} item_t;

typedef struct fifo_queue {
	/* the queue itself, an array of pointers to item structs */
	item_t* *queue;
	/* the head of the queue, the index of the oldest item */
	int head;
	/* the tail of the queue, the index of the next open slot in the queue */
	int tail;
	/* the max_size of the queue */
	int max_size;
} fifo_queue_t;

fifo_queue_t* newQ(int size);

int enqueue(fifo_queue_t *q, int value);

int dequeue(fifo_queue_t *q);