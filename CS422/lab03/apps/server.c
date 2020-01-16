#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#include <unistd.h>
#include <pthread.h>
#define MAX_MSG_LEN 2056
#include "../h/global.h"

//function prototypes
int setup(char*);
char * srecieve(int, char*);
void * handle(void*);
char * getStringArgument(char *, int);
struct prompt_res * arr_to_request(char *);
void sendTrueFalse(bool, int);

//global variables
pthread_mutex_t file_table_lock;
struct file_table_entry * file_table[MAX_FILETABLE_SIZE];
int entryCount = 0;


void sendTrueFalse(bool value, int sock) {
	if (value)
		write(sock, "1\n", 2);
	else
		write(sock, "-1\n", 3);
}
//count is the number of bytes read and size of message
void sendData(int count, char * message, int sock) {
	//count + space + message + '\n' + '0'
	int length = getIntLength(count) + 1 + count + 2;
	char * payload = (char*)malloc(sizeof(char) * length);
	int printed = snprintf(payload, length, "%d %s", count, message);
	payload[printed] = '\n';
	payload[printed + 1] = 0;
	int writtenBytes = write(sock, payload, strlen(payload));
}

int setup(char * port) {
	struct sockaddr_storage their_addr;
    socklen_t addr_size;
    struct addrinfo hints;
	struct addrinfo * results;
    int sock, new_fd;

    memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_INET;  // use IPv4 or IPv6, whichever
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_flags = AI_PASSIVE;     // fill in my IP for me
    getaddrinfo(NULL, port, &hints, &results);

	//make the binded socket, but don't listen yet
	//allow the main loop to delegate listening 
    sock = socket(results->ai_family, results->ai_socktype, results->ai_protocol);
    if (bind(sock, results->ai_addr, results->ai_addrlen) == -1) {
		perror("bind");
		return -1;
	}
	else {
		int yes=1;
		//try and allow resuse
		if (setsockopt(sock, SOL_SOCKET, SO_REUSEADDR, &yes, sizeof yes) == -1) {
			perror("setsockopt");
		}
		if (listen(sock, BACKLOG) == -1) {
			perror("listen");
			return -1;
		}
		return sock;
	}
}
char * srecieve(int sock, char * message) {
	memset(message, 0, MAX_MSG_LEN);
	int recieved = 0;
	bool recievedNewline = false;
	while (!recievedNewline) {
		int length = recv(sock, message, MAX_MSG_LEN, 0);
		if (length <= 0) {
			return NULL;
		}
		//printf("Recieved length: %d\n", length);
		int i = 0;
		//check for newline
		for (i = recieved; i < recieved + length; i++) {
			if (message[i] == '\n') {
				recievedNewline = true;
				break;
			}
		}
	}
	return message;
}

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
    //fflush(stdout);
    filename[newLength-1] = 0;    //null-terminate
    return filename;
}

struct prompt_res * arr_to_request(char * message) {
	int readLen = strlen(message);
	struct prompt_res * result = (struct prompt_res*)malloc(sizeof(struct prompt_res));
	enum Commands command = parseCommand(message, readLen);
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
			char *tmp = getStringArgument(message, readLen);
			result->filename = tmp;
			result->filenameLen = getStringLen(result->filename);
			result->argument = -1;
		}
		else if (command == BACK || command == READ) {
			result->filename = NULL;
			result->filenameLen = -1;
			result->argument = getIntArgument(message, readLen);
		}
		else if (command == CLOS) {
			result->filename = NULL;
			result->argument = -1;
			result->filenameLen = -1;
		}
		return result;
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
void initFileTable() {
	int i = 0;
	pthread_mutex_lock(&file_table_lock);
	for (i = 0; i < MAX_FILETABLE_SIZE; i++) {
		file_table[i] = NULL;
	}
	pthread_mutex_unlock(&file_table_lock);
}

//File table functions
struct file_table_entry * getEntry(char * filename) {
	int i = 0;
	pthread_mutex_lock(&file_table_lock);
	for (i = 0; i < MAX_FILETABLE_SIZE; i++) {
		if (file_table[i] != NULL) {
			struct file_table_entry * entry = file_table[i];
			if (isFilenameEqual(entry->filename, filename)) {
				pthread_mutex_unlock(&file_table_lock);
				return entry;
			}
		}
	}
	pthread_mutex_unlock(&file_table_lock);
	return NULL;
}
bool addEntry(char * filename) {
	int i = 0;
	if (entryCount == MAX_FILETABLE_SIZE) {
		//printf("FILE_TABLE FULL!\n");
		return false;
	}
	pthread_mutex_lock(&file_table_lock);
	for (i = 0; i < MAX_FILETABLE_SIZE; i++) {
		if (file_table[i] == NULL) {
			struct file_table_entry * entry = (struct file_table_entry*)malloc(sizeof(struct file_table_entry));
			entry->filename = filename;
			entry->filesize = getFileSize(filename);
			entry->currentOffset = 0;
			entry->file = fopen(filename, "r");
			file_table[i] = entry;
			entryCount++;
			pthread_mutex_unlock(&file_table_lock);
			return true;
		}
	}
	pthread_mutex_unlock(&file_table_lock);
	return false;
}
bool removeEntry(char * filename) {
	int i = 0;
	pthread_mutex_lock(&file_table_lock);
	for (i = 0; i < MAX_FILETABLE_SIZE; i++) {
		if (file_table[i] != NULL) {
			struct file_table_entry * entry = file_table[i];
			if (isFilenameEqual(entry->filename, filename)) {
				fclose(entry->file);
				free(entry->filename);
				free(entry);
				file_table[i] = NULL;
				entryCount--;
				pthread_mutex_unlock(&file_table_lock);
				return true;
			}
		}
	}
	pthread_mutex_unlock(&file_table_lock);
	return false;
}
bool updateEntry(char * filename, struct file_table_entry * newEntry) {
	if (newEntry == NULL) {
		printf("can't updateEntry with a null entry\n");
		return false;
	}
	int i = 0;
	pthread_mutex_lock(&file_table_lock);
	for (i = 0; i < MAX_FILETABLE_SIZE; i++) {
		if (file_table[i] != NULL) {
			struct file_table_entry * entry = file_table[i];
			if (isFilenameEqual(entry->filename, filename)) {
				file_table[i] = newEntry;
				pthread_mutex_unlock(&file_table_lock);
				return true;
			}
		}
	}
	pthread_mutex_unlock(&file_table_lock);
	return false;
}
char * readFile(char * filename, int count) {
	if (filename == NULL) {
		//printf("can't read from a null filename\n");
		return NULL;
	}
	struct file_table_entry * entry = getEntry(filename);
	if (fseek(entry->file, entry->currentOffset, SEEK_SET) != 0) {
		perror("fseek");
		return NULL;
	}
	//predict length
	int fileLengthLeft = entry->filesize - entry->currentOffset;
	char * buffer;
	int size;
	if (count > fileLengthLeft)
		size = fileLengthLeft;
	else
		size = count;
	//Are we at the end of the file?
	if (size == 0) {
		return NULL;
	}

	buffer = (char*)malloc(sizeof(char) * size);
	int read = fread(buffer, sizeof(char), size, entry->file);
	//printf("read %d bytes from %s bufferSize: %d\n", read, filename, size);
	entry->currentOffset += read;
	updateEntry(filename, entry);
	return buffer;
}
bool back(char * filename, int count) {
	if (filename == NULL) {
		//printf("can't go back on a null filename\n");
		return false;
	}
	struct file_table_entry * entry = getEntry(filename);
	//seek to the currentOffset - count
	if (entry->currentOffset == 0) {
		//printf("we're at the beginning of the file\n");
		return false;
	}
	//int newOffset = ClampLower(0, entry->currentOffset - count);
	if (entry->currentOffset - count < 0) {
		//can't go past the start of the file
		return false;
	}
	if (fseek(entry->file, entry->currentOffset - count, SEEK_SET) != 0) {
		perror("fseek");
		return false;
	}
	entry->currentOffset = entry->currentOffset - count;
	updateEntry(filename, entry);
	return true;
}


void * handle(void * sock) {
	int reciever = *((int *)sock);
	//printf("Handling %d\n", reciever);
	char * activeFile = NULL;
	bool active = true;
	char * message = (char*)malloc(sizeof(char) * MAX_MSG_LEN);
	while (active) {
		message = srecieve(reciever, message);
		if (message == NULL) {
			active = false;
			break;
		}
		//printf("recieved: %s", message);
		struct prompt_res * request = arr_to_request(message);
		//print_prompt_res(request);
		if (isValidRequest(request)) {
			switch (request->command) {
				case OPEN:
					if (activeFile != NULL)
						sendTrueFalse(false, reciever);
					else if (doesFileExist(request->filename)) {
						if (getEntry(request->filename) != NULL) {
							sendTrueFalse(false, reciever);
						}
						else {
							if (addEntry(request->filename)) {
								activeFile = request->filename;
								sendTrueFalse(true, reciever);
							}
							else
								sendTrueFalse(false, reciever);
						}
					}
					else
						sendTrueFalse(false, reciever);
					break;
				case CLOS:
					if (activeFile == NULL)
						sendTrueFalse(false, reciever);
					else {
						if (removeEntry(activeFile)) {
							activeFile = NULL;
							sendTrueFalse(true, reciever);
						}
						else {
							//printf("Couldn't close file, removeEntry returned false\n");
							sendTrueFalse(false, reciever);
						}
					}
					break;
				case READ:
					if (activeFile == NULL) 
						sendTrueFalse(false, reciever);
					else {
						char * message = readFile(activeFile, request->argument);
						if (message == NULL) {
							sendTrueFalse(false, reciever);
						}
						else {
							sendData(strlen(message), message, reciever);
						}
					}
					break;
				case BACK:
					if (activeFile == NULL)
						sendTrueFalse(false, reciever);
					else {
						sendTrueFalse(back(activeFile, request->argument), reciever);
					}
					break;
				default:
					sendTrueFalse(false, reciever);
			}
			//sendTrueFalse(true, reciever);
		}
		else {
			sendTrueFalse(false, reciever);
		}
	}
	//shutdown(reciever, SHUT_RDWR);
	//printf("Closing %d\n", reciever);
	close(reciever);
	return NULL;
}

int main(int argc, char *argv[]) {
	char * port;
	if (argc < 2) {
		printf("USAGE: SERVER_PORT_NUMBER\n");
		return -1;
	}
	port = argv[1];
	//printf("Listening on port: %s\n", port);
	pthread_mutex_init(&file_table_lock, NULL);
	initFileTable();
	int masterSock = setup(port);
	if (masterSock < 0) {
		printf("Failed to bind to port!\n");
		return -1;
	}
	else {
		//printf("Successfully binded to port!\n");
	}
	//accept an awaiting socket
	//create a new thread and give it the socket to accept data from
	while (true) {
		struct sockaddr_storage recv_addr;
		socklen_t size = sizeof(recv_addr);
		//blocking call, responds when we get a byte
		int newSock = accept(masterSock, (struct sockaddr *)&recv_addr, &size);
		//printf("new socket: %d\n", newSock);
		if (newSock < 0) {
			perror("accept");
			//printf("Failed to accept socket!\n");
		}
		else {
			pthread_t thread;
			int * sock_arg = (int*)malloc(sizeof(int));
			*sock_arg = newSock;
			if(pthread_create(&thread, NULL, handle, (void*)sock_arg)) {
				//printf("Unable to create handler thread!\n");
				shutdown(newSock, SHUT_RDWR);		//close the new socket
			}
		}
	}


	if (close(masterSock) < 0)
		//printf("Failed to close master socket\n");
		perror("close");
	return 0;

}
