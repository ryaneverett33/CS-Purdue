#include <stdlib.h>
#include <stdio.h>
#include "fifo-queue.h"

//true/false for auxilary functions
#define auxTrue 1
#define auxFalse 0

int isQueueFull(fifo_queue_t *q) {
	int i;
	for (i = 0; i < q->max_size; i++) {
		if(q->queue[i] == NULL) {
			return auxFalse;
		}
	}
	return auxTrue;
}
int findEmptySpot(fifo_queue_t *q) {
	int i;
	if (q->queue[q->tail] == NULL) {
		return q->tail;
	}
	//check from start for null
	for (i = 0; i < q->max_size; i++) {
		if(q->queue[i] == NULL) {
			return i;
		}
	}
	return -1;
}

/* Create and return a newly allocated empty fifo_queue, with head and tail set to 0,
and the max_size initialized as given size. The queue array should also be allocated
within the struct, of the size max_size. Every element of the queue array should be
set to NULL
Parameters:
	max_size - the maximum number of elements that the queue should be able to hold
	(i.e. the size of the array)
Return:
	A pointer to an allocated and initialized fifo_queue struct. Return NULL if memory
	allocation failed. */
fifo_queue_t* newQ(int size) {
	puts("creating a new queue");
	fifo_queue_t *newQ = malloc(sizeof(fifo_queue_t));
	item_t* array = malloc(sizeof(item_t) * size);
	newQ->queue = array;
	newQ->queue = malloc(sizeof(item_t) * size);
	int i;
	puts("setting to NULL");
	for (i = 0; i < size; i++) {
		newQ->queue[i] = NULL;
		//newQ->queue[i] = malloc(sizeof(item_t));
	}
	//puts("setting properties");
	newQ->max_size = size;
	newQ->head = 0;
	newQ->tail = 0;
	return newQ;
}
/* This function adds (enqueues) a newly allocated item to the queue with the value given.
The item should be added to the end/tail of the queue, increasing tail accordingly. If
tail is at the end of the array, but the queue is not full, it should wrap back around
to the beginning. You will have to allocate a new item struct to store the value given
as well.
Parameters:
	q - the queue to which the newly allocated item will be added
	value - the integer value to store in the queue, within an item struct
Return:
	0 if successful (the item was added), -1 otherwise (if the queue is full, or allocation
	failure occurs) */
int enqueue(fifo_queue_t *q, int value) {
	puts("enqueue: creating new item");
	item_t* item = malloc(sizeof(item_t));
	if (item == NULL) {
		puts("enqueue: Malloc failed!");
		return -1;
	}
	item->value = value;
	if (q == NULL) {
		puts("enqueue: queue argument is NULL");
		return -1;
	}
	else if (q->tail == (q->max_size - 1)) {
		//check for wrap around
		if (isQueueFull(q)) {
			puts("enqueue: queue is full");
			return -1;
		}
		else {
			//queue isn't full, wrap around
			int nextIndex = findEmptySpot(q);
			if (nextIndex == -1) {
				puts("enqueue: Queue isn't full, but there's no empty spots");
				return -1;
			}
			else {
				q->queue[nextIndex] = item;
				q->tail = nextIndex + 1;
				puts("enqueue: added item after wraparound");
				return 0;
			}
		}
	}
	else {
		q->queue[q->tail] = item;
		q->tail++;
		puts("enqueue: added item");
		return 0;
	}
	return -1;
}
/* This function removes the oldest item from the queue (the item at the front/head of 
the queue), and returns the value stored within. When the item is removed, head should
be increased to point to the next item in the queue (or to the spot tail points to,
if empty), and the removed item should be set to NULL and deallocated. If head is at the
end of the array, it should wrap around to the beginning.
Parameters:
	q - the queue from which we are removing an item
Return
	The integer value from the value removed. If the queue is empty, just return 0.*/
int dequeue(fifo_queue_t *q) {
	return 0;
}
