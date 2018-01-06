
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

/*
 *  Please write down a typedef of the following three comparing 
 *  functions: ascending_order, descending_order, special_order.
 *  The type name should be CMP_FUNC.
 */
typedef int (*CMP_FUNC)(int,int);

/*
 *  Do not modify these comparing functions
 */ 
int ascending_order(int a, int b)
{
    return (a-b);
}

int descending_order(int a, int b)
{
    return (b-a);
}

int special_order(int a, int b)
{
    if (a == 0 || b == 0)
        return 0;
    return (a%b);
}

/*
 *  Please implement the bubble sort function that uses
 *  the CMP_FUNC to do the sorting.
 *
 *  Do the bubble sort from the index 0 of the array 'numbers'.
 *  Compare each pair of neighboring elements in the array
 *  and swap them if cmp(a, b) is larger than 0,
 *  where the index of a in 'numbers' is smaller than b
 *
 */
void bubble_sort(int *numbers, int count, CMP_FUNC cmp)
{
	int i;
	int didSwap = 1;
	if (cmp == ascending_order) {
		while(didSwap) {
			for (i = 1; i < count; i++) {
				if (i-1 == 0) {
					didSwap = 0;
				}
				if (cmp(numbers[i - 1],numbers[i]) > 0) {
					int tmp = numbers[i - 1];
					numbers[i - 1] = numbers[i];
					numbers[i] = tmp;
					didSwap = 1;
				}
			}	
		}
		return;
	}
	else if (cmp == descending_order) {
		while(didSwap) {
			for (i = 0; i < count; i++) {
				if (i == 0) {
					didSwap = 0;
				}
				if (cmp(numbers[i],numbers[i+1]) > 0) {
					int tmp = numbers[i + 1];
					numbers[i + 1] = numbers[i];
					numbers[i] = tmp;
					didSwap = 1;
				}
			}
		}
	}
	else if (cmp == special_order) {
		return;
		while(didSwap) {
			for (i = 0; i < count; i++) {
				if (i == 0) {
					didSwap = 0;
				}
				if (cmp(numbers[i],numbers[i+1]) == 0) {
					int tmp = numbers[i + 1];
					numbers[i + 1] = numbers[i];
					numbers[i] = tmp;
					didSwap = 1;
				}
			}
		}
	}
}


/*
 *  Do NOT change the code between here and the end of the file.
 */
void print_numbers(int *numbers, int len)
{
    int i = 0;

    if (numbers == NULL) {
        return;
    }

    for (i = 0; i < len; i++) {
        printf("%d ", numbers[i]);
    }
    printf("\n");
}

int main(int argc, char *argv[])
{
    char *usage = "sort_array <numbers>\nE.g., sort_array 1 2 5 4 3\n";
    int count = argc - 1;
    int *numbers = NULL;
    int i = 0;

    if (argc < 2) {
        printf("%s", usage);
        exit(1);
    }
    
    numbers = (int*)malloc((argc-1) * sizeof(int));
    assert(numbers != NULL);
	
    for (i = 0; i < count; i++) {
        *(numbers+i) = atoi(argv[i+1]);
    }
    
    printf("Original: ");
    print_numbers(numbers, count);

    bubble_sort(numbers, count, ascending_order);
    printf("Ascending: ");
    print_numbers(numbers, count);
    
    bubble_sort(numbers, count, descending_order);
    printf("Descending: ");
    print_numbers(numbers, count);
    
    bubble_sort(numbers, count, special_order);
    printf("Special: ");
    print_numbers(numbers, count);

    free(numbers);

    return 0;
}



