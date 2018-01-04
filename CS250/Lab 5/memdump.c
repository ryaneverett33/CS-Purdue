#include <stdio.h>
#include <string.h>
#include <stdlib.h>

void memdump(char * p , int len) {
    // Add your code here.
    int i = 0, j = 0;
	char* newp = p;
	for (i = 0; i < len; i = i + 16 ) {
		//print address
		printf("%p: ", newp);
		for (j = 0; j < 16; j++) {
			//Print Hex byte
			if (*newp == 0) {
				//format as double 0
				printf("00 ");
			}
			else if (*newp < 16) {
				//format as 0X
				printf("0%x ", *newp);
			}
			else {
				printf("%x ", *newp);
			}
			newp = newp + 1;
		}
		newp = newp - 16;
		for (j = 0; j < 16; j++) {
			//Print formatted ASCII
			if (*newp >=32 && *newp <= 127) {
				printf("%c", *newp);
			}
			else {
				printf(".");
			}
			newp = newp + 1;
		}
		printf("\n");
	}
	/*for (i = 0; i < len; i= i +1) {
		//Print Hex byte
		printf("%x ", *newp);
		newp = newp + 1;
	}*/
	/*newp = p;
	for (i = 0; i < len; i = i + 1) {
		if (*newp >=32 && *newp <= 127) {
			printf("%c", *newp);
		}
		else {
			printf(".");
		}
		newp = newp + 1;
	}*/
}

struct X{
  char a;
  int i;
  char b;
  int *p;
};

struct List {
  char * str;
  struct List * next;
};

int main() {
  char str[20];
  int a = 5;
  int b = -5;
  double y = 12;
  struct X x;
  struct List * head;

  x.a = 'A';
  x.i = 9;
  x.b = '0';
  x.p = &x.i;
  strcpy(str, "Hello world\n");
  printf("&str=0x%x\n", &str);								//str
  printf("&a=0x%x\n", &a);									//a
  printf("&b=0x%x\n", &b);									//b	
  printf("&y=0x%x\n", &y);									//Moved
  printf("&x=0x%x\n", &x.a);
  printf("&x.i=0x%x\n", &x.i);								//x.i
  printf("&x.b=0x%x\n", &x.b);								//x.b
  printf("&x.p=0x%x\n", &x.p);								//x.p
  
  
  //memdump((char *) &x.a, 64);
  head = (struct List *) malloc(sizeof(struct List));
  head->str=strdup("Welcome ");
  head->next = (struct List *) malloc(sizeof(struct List));
  head->next->str = strdup("to ");
  head->next->next = (struct List *) malloc(sizeof(struct List));
  head->next->next->str = strdup("cs250");
  head->next->next->next = NULL;
  printf("&head=0x%x\n", head);
  printf("&head->str=0x%x\n", head->str);					//head->str
  printf("&head->next=0x%x\n", head->next);					//head->next
  printf("&head->next->str=0x%x\n", head->next->str);					//head->next->str
  printf("&head->next->next=0x%x\n", head->next->next);					//head->next->next
  printf("&head->next->next->str=0x%x\n", head->next->next->str);					//head->next->next->str
  printf("&head->next->next->next=0x%x\n", head->next->next->next);					//head->next->next->next
  memdump((char *) &x.a, 64);
  memdump((char*) head, 128);
  //printf("&x=0x%x\n", &x.a);
  //printf("&y=0x%x\n", &y);
}

