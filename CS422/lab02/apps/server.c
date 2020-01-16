/* echoserver.c */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <cnaiapi.h>
#include "c_msg.h"
#include <netinet/in.h>
#include <stdbool.h>
#include <sys/stat.h>
#include <errno.h>
#include <signal.h>
#define FILE_BUFFER_SIZE 1024

connection currentConnection;       //needed for when server is killed (Ctrl-C)

int serializeInt(int value) {
	return (int)htonl((uint32_t)value);
}
int deserializeInt(int value) {
    return (int)ntohl((uint32_t)value);
}
struct c_msg serialize(struct c_msg msg) {
    struct c_msg tmpMessage = msg;
    tmpMessage.mtype = serializeInt(msg.mtype);
    tmpMessage.maxsize = serializeInt(msg.maxsize);
    tmpMessage.actualsize = serializeInt(msg.actualsize);
    return tmpMessage;
}
struct c_msg deserialize(struct c_msg msg) {
    struct c_msg tmpMessage = msg;
    tmpMessage.mtype = deserializeInt(msg.mtype);
    tmpMessage.maxsize = deserializeInt(msg.maxsize);
    tmpMessage.actualsize = deserializeInt(msg.actualsize);
    return tmpMessage;
}

//fills the filename array in the struct from a pointer
//basically a copy
void fillFileName(char * filename, struct c_msg * msg) {
    int i = 0;
	for (i = 0; i < C_FILENAME_LEN; i++) {
		if (i < strlen(filename))
			msg->filename[i] = filename[i];
		else
			msg->filename[i] = 0;
	}
}
struct c_msg makeMessage(char * filename, int maxfilesize, int mtype, int actualsize) {
	struct c_msg req;
	req.mtype = mtype;
	fillFileName(filename, &req);
	req.maxsize = maxfilesize;
	req.actualsize = actualsize;
	return req;
}
struct c_msg recieveMessage(connection conn) {
    //char * buffer = (char *)malloc(sizeof(char) * BUFFSIZE);
    struct c_msg msg;
    int length = 0;
    //int index = 0;
    int contentLength = (int)sizeof(struct c_msg);
    while (length != contentLength) {
        int recievedLen = recv(conn, (char *)&msg, sizeof(struct c_msg), 0);
        if (DEBUG)
            printf("length was %d, adding %d ACTUAL CONTENT LENGTH: %d\n", length, recievedLen, contentLength);
        length += recievedLen;
    }
    return msg;
}
void sendFile(connection conn, char * filename) {
    FILE * file = fopen(filename, "r");
    char * buff = (char*)malloc(sizeof(char) * FILE_BUFFER_SIZE);
    int read = 0;
    while ((read = fread(buff, sizeof(char), FILE_BUFFER_SIZE, file)) > 0) {
        if (DEBUG)
            printf("SERVER: Read %d bytes from %s\n", read, filename);
        //write bytes to stream
        //send(conn, (const void *)&doesNotExistResponse, sizeof(struct c_msg), 0);
        send(conn, buff, read, 0);
    }
    if (DEBUG)
        printf("successfully sent file to client\n");
}

int getFileSize(char * filename) {
    struct stat st;
    stat(filename, &st);
    return st.st_size;
}
bool doesFileExist(char * filename) {
    struct stat st;
    return (stat(filename, &st) == 0);
}
void handleDeath(int signum) {
    //Works on lore, but program won't bind after a successful transfer on linux
    //Have to wait a little bit (time varies) before bind will succeed
    if (shutdown(currentConnection, SHUT_RDWR) == -1)
        close(currentConnection);
    exit(-1);
}

int main (int argc, char *argv[])
{
    signal(SIGINT, handleDeath);
    connection	conn;
	int		recvLen;                //length of recieved data
    int     portNum;                //port number to bind to and use

	if (argc != 2) {
		(void) fprintf(stderr, "usage: %s SERVER_APPLICATION_NUMBER\n", argv[0]);
		exit(1);
	}
    portNum = atoi(argv[1]);
    while (true) {
        conn = await_contact((appnum)portNum);
        currentConnection = conn;
        if (conn < 0)
            exit(1);
        struct c_msg message = recieveMessage(conn);
        message = deserialize(message);
        if (DEBUG)
            printf("Recieved message, filename: %s, maxfilesize: %d, type: %d\n", message.filename, message.maxsize, message.mtype);
        if (doesFileExist((char*)&(message.filename))) {
            int size = getFileSize(&message.filename);
            if (size > message.maxsize) {
                if (DEBUG)
                    printf("File too big, maxsize: %d, filesize: %d\n", message.maxsize, size);
                //send file too big
                struct c_msg fileTooBigResponse = makeMessage(&message.filename, message.maxsize, C_ERR, size);
                //set actualsize to size
                fileTooBigResponse.actualsize = size;

                fileTooBigResponse = serialize(fileTooBigResponse);
                send(conn, (const void*)&fileTooBigResponse, sizeof(struct c_msg), 0);
            }
            else {
                if (DEBUG)
                    printf("Server ready to send file\n");
                    //same filename, actualsize of file
                struct c_msg readyForTransferMessageResponse = makeMessage(&message.filename, message.maxsize, C_RESPONSE, size);
                //set actualsize to size
                readyForTransferMessageResponse.actualsize = size;

                readyForTransferMessageResponse = serialize(readyForTransferMessageResponse);
                send(conn, (const void*)&readyForTransferMessageResponse, sizeof(struct c_msg), 0);
                sendFile(conn, &message.filename);
            }
        }
        else {
            //send file does not exist
            struct c_msg doesNotExistResponse = makeMessage(&message.filename, message.maxsize, C_ERR, 0);
            //set actualsize to 0
            doesNotExistResponse.actualsize = 0;

            doesNotExistResponse = serialize(doesNotExistResponse);
            send(conn, (const void *)&doesNotExistResponse, sizeof(struct c_msg), 0);
        }
        //wait for request
            //if file does not exist, reply back with err (same filename, actualsize 0)
            //if file too big, send err (filename same, actualsize size of file)
            //if file acceptable, send response (filename same, actualsize size of file)
        //wait for request
        send_eof(conn);
    }
    
    return 0;
}
