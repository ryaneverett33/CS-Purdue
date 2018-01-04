#include <stdio.h>
//#include <malloc.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <string.h>


#define READABLE_FILE "file_to_read.txt" /* File to be read during read operations */
#define BYTES_TO_READ_WRITE 819200 /* 800 KB */
#define MAX_BUFFER 1048576 /* 1 MB*/

/* Function for write without buffer */
void mywritec(char);

/* Functions for write with buffer */
void mywritebufsetup(int);
void myputc(char);
void mywriteflush(void);

/* Function for read without buffer */
int myreadc(void);

/* Functions for read with buffer */
void myreadbufsetup(int);
int mygetc(void);

/* Declare global variables for write operations here */
int fd_write = 1;
char write_buf[MAX_BUFFER];
char* wp = &write_buf[0];
int write_buf_size;
int wrPoint = 0;

/* Declare global variables for read operations here */
int fd_read;
char read_buf[MAX_BUFFER];
char* rp = &read_buf[0];
int read_buf_size;
int rePoint = 0;
int read_count = 0;

/* Main function starts */
int main()
{
    clock_t begin, end;
    int option, n, temp;
    const char *a="Writing byte by byte\n";
    const char *b="Writing using buffers\n";
    unsigned long i, bytes_to_write = BYTES_TO_READ_WRITE, bytes_to_read = BYTES_TO_READ_WRITE;
    char ch;

    while(1)
    {
        printf("\n 1 - Write without buffering \n 2 - Write with buffering");
        printf("\n 3 - Read without buffering \n 4 - Read with buffering");
        printf(("\n 5 - Exit \n Enter the option: "));
        scanf("%d", &option);
        switch(option)
        {
            case 1: /* Write without buffer */
                begin = clock();
                for (i=0;i<bytes_to_write;i++)
                {
                    ch = a[i%strlen(a)];
                    mywritec(ch);
                }
                end = clock();
                printf("\n Time to write without buffering: %f secs\n",(double)(end - begin)/CLOCKS_PER_SEC);
                break;

            case 2:  /* Write with buffer */
                printf("\n Enter the buffer size in bytes: ");
                scanf("%d", &n);
                mywritebufsetup(n);
                begin = clock();
                for (i=0;i<bytes_to_write;i++)
                {
                    ch = b[i%strlen(b)];
                    myputc(ch);
                }
                mywriteflush();
                end = clock();
                printf("\n Time to write with buffering: %f secs\n",(double)(end - begin)/CLOCKS_PER_SEC);
                break;

            case 3:  /* Read without buffer */
                fd_read = open(READABLE_FILE, O_RDONLY);
                if(fd_read < 0)
                {
                    printf("\n Error opening the readable file \n");
                    return 1;
                }
                begin = clock();
                for (i=0;i<bytes_to_read;i++)
                {  /* you may need to modify this slightly to print the character received and also check for end of file */
                    if(myreadc() == -1)
                    {
                        printf("\n End of file \n");
                        break;
                    }
                }
                end = clock();
                if(close(fd_read))
                {
                    printf("\n Error while closing the file \n ");
                }
                printf("\n Time to read without buffering: %f secs\n",(double)(end - begin)/CLOCKS_PER_SEC);
                break;

            case 4:  /* Read with buffer */
                printf("\n Enter the buffer size in bytes: ");
                scanf("%d", &n);
                myreadbufsetup(n);
                fd_read = open(READABLE_FILE, O_RDONLY);
                if(fd_read < 0)
                {
                    printf("\n Error opening the readable file \n");
                    return 1;
                }
                begin = clock();
                for (i=0;i<bytes_to_read;i++)
                { /* you may need to modify this slightly to print the character received and also check for end of file */
                    int gets = mygetc();
                    if(gets == -1)
                    {
                        printf("\n End of file \n");
                        break;
                    }
                    /*else {
                    	printf("%c", gets);
                    }*/
                }
                end = clock();
                if(close(fd_read))
                {
                    printf("\n Error while closing the file \n ");
                }
                printf("\n Time to read with buffering: %f secs\n",(double)(end - begin)/CLOCKS_PER_SEC);
                break;

            default:
                return 0;
        }
    }
}
/* Function for write without buffer */
void mywritec(char c) {
	char arr[1] = { c };
	int writen = write(1, arr, 1);
}

/* Functions for write with buffer */
void mywritebufsetup(int n) {
	if (n <= 0) {
		//https://www.xkcd.com/221/
		printf("Number is less than or equal to 0, using 4 which was chosen by a fair dice roll. guaranteed to be random.\n");
		write_buf_size = 4;
	}
	else if (n > MAX_BUFFER) {
		//https://www.xkcd.com/221/
		printf("Number is greater than MAX_BUFFER, using 4 which was chosen by a fair dice roll. guaranteed to be random.\n");
		write_buf_size = 4;
	}
	else {
		write_buf_size = n;
	}
    read_count = 0;
}
void myputc(char c){
	//puts("Increasing wrPointer");
	write_buf[wrPoint] = c;
	wp = &write_buf[wrPoint];
	//printf("char* %c ", *wp);
	wrPoint = wrPoint + 1;
	if (wrPoint == write_buf_size) {
		//puts("Writing out");
		write(1, write_buf, wrPoint);
		wrPoint = 0;
	}
}
void mywriteflush(){
	//puts("Flushing");
	write(1, write_buf, wrPoint);
	wrPoint = 0;
	wp = &write_buf[0];
}

/* Function for read without buffer */
int myreadc() {
	char buf[1];
	int haveRead = read(fd_read, buf, 1);
	//printf("Read: %d, %c", haveRead, buf[0]);
	if (haveRead <= 0) {
		return -1;
	}
	else {
		return buf[0];
	}
}

/* Functions for read with buffer */
void myreadbufsetup(int n){
	if (n <= 0) {
		//https://www.xkcd.com/221/
		printf("Number is less than or equal to 0, using 4 which was chosen by a fair dice roll. guaranteed to be random.\n");
		read_buf_size = 4;
	}
	else if (n > MAX_BUFFER) {
		//https://www.xkcd.com/221/
		printf("Number is greater than MAX_BUFFER, using 4 which was chosen by a fair dice roll. guaranteed to be random.\n");
		read_buf_size = 4;
	}
	else {
		read_buf_size = n;
	}
    read_count = 0;
    rePoint = 0;
}
int mygetc() {
    //refresh the buffer
    if (read_count <= 0) {
        read_count = read(fd_read, read_buf, read_buf_size);
        rp = &read_buf[0];
        rePoint = 0;
    }
    if (read_count == 0) {
        return -1;
    }
    else {
        char c = read_buf[rePoint];
        /*if (c == '?') {
            printf("c: %d, read_count: %d, *rp: %c rePoint: %d\n", c, read_count, *rp, rePoint);
        }*/
        //printf("%c", c);
        read_count = read_count - 1;
        rp = &read_buf[rePoint + 1];
        rePoint = rePoint + 1;
        //printf("rp: %c\n", *rp);
        //return c;
        //Don't know why we do this...
        return c & 0x0000FFFF;
    }
}

