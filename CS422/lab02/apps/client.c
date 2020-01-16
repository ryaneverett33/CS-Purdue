/* client.c */

#include <stdlib.h>
#include <stdio.h>
#include <cnaiapi.h>
#include <string.h>
#include "c_msg.h"
#include <netinet/in.h>
#include <errno.h>
#define FILE_BUFFER_SIZE 1024
int readln (char *, int);

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
			printf("Recieved %d/%d bytes from server\n", recievedLen, contentLength);
        length += recievedLen;
    }
    return msg;
}

void writeFileTooBig(int size) {
	FILE * f = fopen("output.data", "w");
	if (f == NULL) {
		printf("Error opening file: %s\n", strerror(errno));
		return;
	}	
	fprintf(f, "ERROR - File Too Big. Size is %d bytes\n", size);
	fclose(f);
}
void writeFileNotFound() {
	FILE * f = fopen("output.data", "w");
	if (f == NULL) {
		printf("Error opening file: %s\n", strerror(errno));
		return;
	}	
	fprintf(f, "ERROR - File Does Not Exist\n");
	fclose(f);
}
void recieveFile(connection conn, int actualsize) {
    //writes file of size actualsize to output.data
	char * buff = (char *)malloc(sizeof (char) * FILE_BUFFER_SIZE);
    FILE * f = fopen("output.data", "w");
	if (f == NULL) {
		printf("Error opening file: %s\n", strerror(errno));
		send_eof(conn);
		return;
	}
	int length = 0;
	while (length != actualsize) {
		int recievedLen = recv(conn, buff, sizeof(char) * FILE_BUFFER_SIZE, 0);
		length += recievedLen;
		if (DEBUG)
			printf("CLIENT recieved %d/%d bytes of file\n", length, actualsize);
		fwrite(buff, sizeof(char), recievedLen, f);
	}
	if (DEBUG)
		printf("Successfully transferred file from server to output.data\n");
}

int main (int argc, char *argv[])
{
	computer 	comp;
	appnum		app;
	connection	conn;
	char * 		filename;
	int			maxfilesize;

	if (argc < 5) {
		(void) fprintf(stderr, "usage: %s SERVER_IP_ADDRESS SERVER_APPLICATION_NUMBER FILE_NAME MAX_FILE_SIZE\n",
			       argv[0]);
		exit(1);
	}

	comp = cname_to_comp(argv[1]);
	if (comp == -1)
		exit(1);
	app = (appnum)atoi(argv[2]);
	filename = argv[3];
	maxfilesize = atoi(argv[4]);

	if (DEBUG) {
		printf("ip: %d, port: %d, filename: %s, maxfilesize: %d\n", comp, app, filename, maxfilesize);
	}
	conn = make_contact(comp, app);
	if (conn < 0) 
		exit(1);
	//make request struct

	struct c_msg request = makeMessage(filename, maxfilesize, C_REQUEST, 0);
	if (DEBUG)
		printf("request: filename: %s, maxfilesize: %d, actualsize: %d\n", request.filename, request.maxsize, request.actualsize);
	//set maxfilesize to maxfilesize
	request.maxsize = maxfilesize; 

	request = serialize(request);
	send(conn, (const void*)&request, sizeof(struct c_msg), 0);
	if (DEBUG)
		printf("Sent request\n");
	struct c_msg response = recieveMessage(conn);
	if (DEBUG)
		printf("Recieved response\n");
	response = deserialize(response);
	if (DEBUG)
		printf("response: filename: %s, maxfilesize: %d, actualsize: %d, mtype: %d\n", response.filename, response.maxsize, response.actualsize, response.mtype);
	//if file does not exist: C_ERR, filename (same), actualsize: 0
	//if file too big: C_ERR, filename(same), actualsize: size in bytes
	if (response.mtype == C_ERR) {
		if (response.actualsize == 0) {
			//file does not exist
			if (DEBUG)
				printf("File not found!\n");
			writeFileNotFound();
		}
		else {
			//file too big
			if (DEBUG)
				printf("File too big!\n");
			writeFileTooBig(response.actualsize);
		}
	}
	else if (response.mtype == C_RESPONSE) {
		//prepare for file transfer
		if (DEBUG)
			printf("Waiting for file transfer\n");
		recieveFile(conn, response.actualsize);
	}
	
	
	//get requested file from user
	//send request message to server (C_REQUEST, filename, maxsize)
		//if file does not exist output.file >> "ERROR - File Does Not Exist"
		//if file too big output.file >> "ERROR - File Too Big. Size is X bytes"
	//wait for response
		//prep file for writing
	//write data to file until totallen is met
	return 0;
}

