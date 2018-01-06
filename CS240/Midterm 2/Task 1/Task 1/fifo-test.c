#include <stdlib.h>
#include <stdio.h>
#include "fifo-queue.h"

void printQueue(fifo_queue_t* queue) {
	int i;
	for (i = 0; i < queue->max_size; i++) {
		if (queue->queue[i] != NULL) {
			printf("Value: %d, Index: %d\n", queue->queue[i]->value, i);
		}
		else {
			printf("i: %d\n", i);
		}
	}
}
int main() {
	fifo_queue_t* queue = newQ(5);
	printf("Queue size: %d\n", queue->max_size);
	printf("Head: %d, Tail: %d\n", queue->head, queue->tail);
	printf("size of queue: %lud\n", sizeof(queue));
	if(enqueue(queue, 24) == -1) {
		puts("Failed to add item when should have");
	}
	enqueue(queue, 5);
	printQueue(queue);
	return 1;
}