#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void print_triangle(int side, int height);

void print_triangle(int side, int height) {
        int i, j, counter;
         counter = 0;
         printf("\n");
         for (i = 0; i < height; i++) {
                 for (j = 0; j < height; j++) {
                         //char c = ((side = 1) ? (j > counter ? ' ' : '*') : (side = 2) ? ((height - j) > (counter + 1) ? ' ' : '*') : '\0');
						 char c;
						 if (side == 1) {
							 if (j > counter) {
								c = ' ';
							 }
							 else {
								c = '*';
							 }
						 }
						 else if (side == 2) {
							 if (height - j > (counter + 1)) {
								 c = ' ';
							 }
							 else {
								 c = '*';
							 }
						 }
                         printf("%c", c);
                 }
                 printf("\n");
                 counter++;
        }
 }

int main(int argc, char** argv) {
         int side, height;
         char* response = (char*)malloc(16* sizeof(char));
        int firstrun = 1;

         while (1) {
                 while (!(!strcmp(response, "y") || !strcmp(response, "n")))
                          {
                         if (!firstrun) {
                                 printf("\nDo you want to continue? [y/n]: ");
                                 scanf("%s", response);
                         } else {
                                 printf("Draw Right Angle Triangle\n");
                                 strcpy(response, "y");
                                 firstrun = 0;
                         }
                 }
                 if (!strcmp(response, "n")) {
                         free(response);
                         return 0;
                 }
                 *response = '\0';
                 printf("\nPlease enter your choice of right triangle\n");
                 printf("1 for left aligned right angle triangle\n");
                 printf("2 for right aligned right angle triangle\n");
                 while (!(!strcmp(response, "1") || !strcmp(response, "2"))) {
                         printf("\nEnter your choice [1/2]: ");
                         scanf("%s", response);
                 }
                 side = atoi(response);
                 *response = '\0';
                 height = -2;
				 //printf("%i",height < 0 || height > 100);
                 while (height < 0 || height > 100) {
                        printf("\nEnter the height of the triangle [0-100]: ");
                        scanf("%d", &height);
//                      scanf("%s", response);
//                      fflush(stdin);
//                      getchar();
                }
                print_triangle(side, height);
        }
}