typedef struct node {
	/* Internal linked list information */
	struct node *next; // Pointer to next node in the list
	struct node *prev; // Pointer to previous node in the list
	int value; // Data value stored in the node
} DLLItem;

typedef struct linkedlist {
	struct node *head;
	struct node *tail;
} DLList;

// Create a newly allocated empty linkedlist_t with head and tail initialized to NULL
DLList *create_linkedlist();

// Create a new ListNode and assign the value of the node to the parameter value. Add the
// node at the tail of the list
void llist_add(DLList * list, int value);

// Remove the entry with that value in the list.
void llist_remove(DLList * list, int value);

//Group 1
int llist_insertAfter_ith(DLList * list, int ith, int value);
int llist_remove_ith(DLList * list, int ith);
int llist_remove_first(DLList * list);
int llist_remove_last(DLList * list);
void llist_insert_first(DLList * list, int value);
void llist_insert_last(DLList * list, int value);

//Group 2
DLList *llist_intersection(DLList * list1, DLList * list2);
DLList *llist_union(DLList * list1, DLList * list2);
void llist_sort(DLList * list, int ascending);
void llist_removeRange(DLList * list, int low, int high);

//Aux function
void printList(DLList * list);
void printListInfo(DLList * list);