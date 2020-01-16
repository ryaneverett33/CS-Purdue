#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#include <unistd.h>

#include "../h/global.h"

char * getStringArgument(char *, int);
struct prompt_res * prompt();
const char * command_to_str(enum Commands);
void print_prompt_res(struct prompt_res*);
int connect_to_server(char*, char*);
bool isValidRequest(struct prompt_res*);
char * request_to_arr(struct prompt_res *);

//returns a null-terminated string of max size PROMPT_BUFFER_SIZE
//return 'filename' from 'OPEN filename\n'
//for some reason, this results in invalid memory access when placed in global.c
char * getStringArgument(char * string, int stringLen) {
    if (stringLen < 7) {
        //min acceptable string: 'XXXX a\n' where XXXX is the command of length four
        //must be followed by newline
        return NULL;
    }
    int newLength = stringLen - 5;      //remove 'XXXX '
    char * pointer = string;
    pointer += 5;
    char * filename = (char*)malloc(sizeof(char) * newLength);        //keep new line for null termination
    int i = 0;
	for (i = 0; i < newLength; i++) {
        //copy bytes 1:1 from pointer to filename
        filename[i] = pointer[i];
        //printf("%d f: %c, p: %c\n", i, filename[i], pointer[i]);
        fflush(stdout);
    }
    //printf("copied newLength: %d\n", newLength);
    fflush(stdout);
    filename[newLength-1] = 0;    //null-terminate
    return filename;
}
//connect to the server and return the connected socket, return -1 else
int connect_to_server(char * address, char * port) {
	struct addrinfo hints;
	struct addrinfo * results;
	int sock;

	memset(&hints, 0, sizeof hints);
	hints.ai_family = AF_INET;
	hints.ai_socktype = SOCK_STREAM;
	getaddrinfo(address, port, &hints, &results);

	//Make the socket and connect to the server, return fd
	sock = socket(results->ai_family, results->ai_socktype, results->ai_protocol);
	if (connect(sock, results->ai_addr, results->ai_addrlen) == -1) {
		return -1;
	}
	else {
		return sock;
	}
}

struct prompt_res * prompt() {
	char * buffer = (char*)malloc(sizeof(char*) * PROMPT_BUFFER_SIZE);
	struct prompt_res * result = (struct prompt_res*)malloc(sizeof(struct prompt_res));
	result->filename = NULL;
	result->filenameLen = -1;
	result->argument = -1;
	result->command = INVALID;
	printf("C> ");
	fflush(stdout);
	int readLen = readln(buffer, PROMPT_BUFFER_SIZE);
	if (readLen == 0) {
		//printf("Didn't input any data\n");
	}
	else {
		//Get Command
		enum Commands command = parseCommand(buffer, readLen);
		if (command == INVALID) {
			result->command = command;
			result->filename = NULL;
			result->argument = -1;
			return result;
		}
		else {
			//Get Arguments
			result->command = command;
			if (command == OPEN) {
				char *tmp = getStringArgument(buffer, readLen);
				if (tmp == NULL)
					return NULL;
				result->filename = tmp;
				result->filenameLen = getStringLen(result->filename);
				result->argument = -1;
			}
			else if (command == BACK || command == READ) {
				result->filename = NULL;
				result->filenameLen = -1;
				result->argument = getIntArgument(buffer, readLen);
			}
			else if (command == CLOS) {
				result->filename = NULL;
				result->argument = -1;
				result->filenameLen = -1;
			}
			return result;
		}
	}
}
const char * command_to_str(enum Commands command) {
	switch (command) {
		case OPEN:
			return "OPEN";
		case READ:
			return "READ";
		case BACK:
			return "BACK";
		case CLOS:
			return "CLOS";
		default:
			return "INVALID";
	}
}
void print_prompt_res(struct prompt_res * result) {
	printf("Command: %d, %s\n", result->command, command_to_str(result->command));
	if (result->filename != NULL)
		printf("Filename: %s\n", result->filename);
	printf("filenameLen: %d\n", result->filenameLen);
	printf("argument: %d\n", result->argument);
}
//converts a struct prompt_res to a byte
char * request_to_arr(struct prompt_res * request) {
	int length = 5;	//'XXXX '
	switch (request->command) {
		case OPEN:
			length += request->filenameLen;
			break;
		case READ:
		case BACK:
			length += getIntLength(request->argument) + 1;
		case CLOS:
			length--;	//no space after the command
			break;
		default:		//for case INVALID
			return NULL;
	}
	length++;		//null terminate
	char * message = (char*)malloc(sizeof(char) * length);
	int wrote;
	if (request->command == OPEN)
		wrote = snprintf(message, length, "%s %s", command_to_str(request->command), request->filename);
	else if (request->command == READ || request->command == BACK)
		wrote = snprintf(message, length, "%s %d", command_to_str(request->command), request->argument);
	else if (request->command == CLOS)
		wrote = snprintf(message, length, "%s", command_to_str(request->command));
	message[wrote] = '\n';
	message[wrote + 1] = 0;
	//printf("wrote %d characters, predicted length: %d\n", wrote, length);
	return message;
}
//argument is -1 for OPEN/CLOS, or the numeric value (READ '10') for READ/BACK
char * crecieve(int argument, int sock) {
	char * response;
	int maxsize;
	if (argument == -1) {
		//server should return 1 or -1
		maxsize = 3;//'-1\n' max size
	}
	else {
		//returns the argument (+1 offset), a space, argument length of data, newline
		maxsize = getIntLength(argument) + 2 + argument + 1;
	}
	response = (char*)malloc(sizeof(char) * maxsize);
	int recieved = 0;
	bool recievedNewline = false;
	while (!recievedNewline) {
		int length = recv(sock, response, maxsize, 0);
		int i = 0;
		//check for newline
		for (i = recieved; i < recieved + length; i++) {
			if (response[i] == '\n') {
				response[i+1] = 0;
				recievedNewline = true;
				break;
			}
		}
		recieved += length;
	}
	return response;
}

//SERVER_IP_ADDRESS SERVER_PORT_NUMBER
int main(int argc, char *argv[]){
	char * ip_address;
	char * port;
	if (argc < 3) {
		printf("USAGE: SERVER_IP_ADDRESS SERVER_PORT_NUMBER\n");
		return -1;
	}
	ip_address = argv[1];
	port = argv[2];
	//printf("Connect to address: %s:%s\n", ip_address, port);
	int sock = connect_to_server(ip_address, port);
	if (sock <= 0) {
		printf("Failed to connect to server!\n");
		return -1;
	}

	while (true) {
		struct prompt_res * result = prompt();
		//print_prompt_res(result);
		if (isValidRequest(result)) {
			//send request
			char * payload = request_to_arr(result);
			int sent = write(sock, payload, strlen(payload));
			char * message = crecieve(result->argument, sock);
			printf("S> %s", message);
		}
		else {
			printf("S> -1\n");
		}
	}





	return 0;

}
