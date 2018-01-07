char* usage =
"usage for myhttpd:\n"
"Options: [-f|-t|-p|empty] [port|empty]\n"
"	-f: Serves a request with a new process\n"
"	-t: Use dem threads for handlin't\n"
"	-p: How about a whole bunch of threads\n"
"		empty: nothing special, lame\n"
"	port: 1024 < port < 65536\n"
"		empty: a default port of 16969 is used\n";

#include <pthread.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include <sys/stat.h>
#include <netinet/in.h>
#include <netdb.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <iostream>
#include <dirent.h>
#include <errno.h>
#include <algorithm>
#include <vector>
#include <signal.h>
#include "Sender.hh"
#include "FileInfo.hh"
#include "CgiRunner.hh"
#include "Stats.hh"
#include "Timer.hh"
#include "Logger.hh"

using namespace std;

pthread_mutex_t mutex;
pthread_mutexattr_t mutex_attr;
Sender * sender;
Stats stats;
Logger logger;

bool containsDots(char* message) {
	char * copy = message;
	char last;
	last = 0;
	/*while (copy != NULL || *copy != 0) {
		fprintf(stderr, "%c", *copy);
		if (*copy == '.' && last == '.') {
			return true;
		}
		last = *copy;
		copy++;
	}*/
	int len = strlen(message);
	for (int i = 0; i < len; i++) {
		fprintf(stderr, "%c", *copy);
		if (*copy == '.' && last == '.') {
			return true;
		}
		last = *copy;
	}
	return false;
}
bool wrongIndex(char * message) {
	if (strcmp(message, "/") == 0) {
		return true;
	}
	return false;
}

void sendFile(FILE * file, int socket, char * document_type) {
	/*Write success*/
	write(socket, "HTTP/1.1 200 OK", 15);
	write(socket, "\r\n", 2);
	write(socket, "Server: MyServer/1.0", 20);
	write(socket, "\r\n", 2);
	write(socket, "Content-Type ", 13);
	write(socket, document_type, strlen(document_type));
	write(socket, "\r\n\r\n", 4);

	char c;
	long l = 0;
	/*Write file data*/
	while (l = read(fileno(file), &c, sizeof(c))) {
		if (l != write(socket, &c, sizeof(c))) {
			perror("write error");
			return;
		}
	}
}
void sendWrongSecret(int socket) {
	puts("Sending wrong secret");
	write(socket, "HTTP/1.1 404 File Not Found", 27);
	write(socket, "\r\n", 2);
	write(socket, "Server: MyServer/1.0", 20);
	write(socket, "\r\n", 2);
	write(socket, "Content-Type: text/html", 23);
	write(socket, "\r\n\r\n", 4);
	write(socket, "WRONG SECRET", 14);
}
void sendFileNotFound(int socket) {
	puts("Sending 404");
	write(socket, "HTTP/1.1 404 File Not Found", 27);
	write(socket, "\r\n", 2);
	write(socket, "Server: MyServer/1.0", 20);
	write(socket, "\r\n", 2);
	write(socket, "Content-Type: text/html", 23);
	write(socket, "\r\n\r\n", 4);
	write(socket, "File not found", 14);
}
char * getDocumentType(char * line) {
	//GET / HTTPblahblah
	//split line by space, get first word, return it
	char * pch;
	int i = 0;
	pch = strtok(line, " ");
	while (pch != NULL)
	{
		printf("%d:%s\n", i, pch);
		if (i == 0) {
			return strdup(pch);
		}
		printf("%s\n", pch);
		pch = strtok(NULL, " ");
		i++;
	}
	return NULL;
}
char * getRequestName(char * line) {
	//GET / HTTPblahblah
	//split line by space, get middle word, return it
	char * pch;
	int i = 0;
	pch = strtok(line, " ");
	while (pch != NULL)
	{
		printf("%d:%s\n", i, pch);
		if (i == 1) {
			return strdup(pch);
		}
		//printf("%s\n", pch);
		pch = strtok(NULL, " ");
		i++;
	}
	return NULL;
}
//strtok just doesn't work
char * getWordAtSpaceIndex(char * line, int index) {
	int len = strlen(line);
	char * newWord = (char*)malloc(sizeof(char) * len);
	int newLen = 0;
	int spaceCount = 0;
	for (int i = 0; i < len; i++) {
		if (line[i] == ' ') {
			spaceCount++;
			continue;
		}
		if (spaceCount == index) {
			//add to newWord
			newWord[newLen] = line[i];
			newLen++;
		}
	}
	newWord[newLen] = 0;	//null terminate
	return newWord;
}

void signal_callback_handler(int signum) {
	printf("Caught signal SIGPIPE %d\n", signum);
}

// Processes time request
char * processTimeRequest(int socket);
void processTimeRequestThread(int socket);
void threadsPool(int socket);
main(int argc, char ** argv)
{
	signal(SIGPIPE, signal_callback_handler);
   // Add your HTTP implementation here
	int port = 16969;
	int concurrency = 0;
	sender = new Sender();
	if(argc >= 2) {
		if(!strncmp(argv[1], "-", 1)) {
			if(argv[1][1] == 'f') {
				concurrency = 1;
			}
			else if(argv[1][1] == 't') {
				concurrency = 2;
			}
			else if(argv[1][1] == 'p') {
				concurrency = 3;
			}
			else {
				fprintf(stderr, "%s\n", usage);
				exit(1);
			}
		}
		else {
			port = atoi(argv[1]);
		}

		if(argc == 3) {
			port = atoi(argv[2]);
		}

		if(port <= 1024 || port >= 65535) {
			fprintf(stderr, "%s\n", usage);
			exit(1);
		}

		if(argc > 3) {
			fprintf(stderr, "%s\n", usage);
			exit(1);
		}
	}
	fprintf(stderr, "operating mode: %d, port: %d\n", concurrency, port);
	// Set the IP address and port for this server
	struct sockaddr_in serverIPAddress;
	memset(&serverIPAddress, 0, sizeof(serverIPAddress));
	serverIPAddress.sin_family = AF_INET;
	serverIPAddress.sin_addr.s_addr = INADDR_ANY;
	serverIPAddress.sin_port = htons((u_short)port);

	// Allocate a socket
	int masterSocket = socket(PF_INET, SOCK_STREAM, 0);
	if(masterSocket < 0) {
		perror("socket");
		exit(-1);
	}

	// Set socket options to reuse port. Otherwise we will
	// have to wait about 2 minutes before reusing the sae port number
	int optval = 1;
	int err = setsockopt(masterSocket, SOL_SOCKET, SO_REUSEADDR,
		(char *)&optval, sizeof(int));

	// Bind the socket to the IP address and port
	int error = bind(masterSocket,
		(struct sockaddr *)&serverIPAddress,
		sizeof(serverIPAddress));
	if(error) {
		perror("bind");
		exit(-1);
	}

	// Put socket in listening mode and set the 
	// size of the queue of unprocessed connections
	error = listen(masterSocket, 10);
	if(error) {
		perror("listen");
		exit(-1);
	}
	if(concurrency == 3) {
		pthread_mutexattr_init(&mutex_attr);
		pthread_mutex_init(&mutex, &mutex_attr);
		pthread_t t[10];
		pthread_attr_t attr;
		pthread_attr_init(&attr);
		pthread_attr_setscope(&attr, PTHREAD_SCOPE_SYSTEM);

		for(int i = 0; i < 10; i++) {
			pthread_create(&t[i], &attr, (void * (*)(void *))threadsPool, (void *)masterSocket);
		}

		pthread_join(t[0], NULL);
	}
	
	while(1) {
		// Accept incoming connections
		struct sockaddr_in clientIPAddress;
		int alen = sizeof(clientIPAddress);
		int slaveSocket = accept(masterSocket,
			(struct sockaddr *)&clientIPAddress,
			(socklen_t*)&alen);

		if(slaveSocket < 0) {
			if (errno == EINTR) {
				puts("Accept was interrupted, redo!");
				continue;
			}
			else {
				puts("Accept was canceled, can't redo");
				perror("accept");
				exit(-1);
			}
		}

		if(concurrency == 0) {
			Timer timer;
			double start = timer.elapsed();
			puts("Processing with thread");
			char * request = processTimeRequest(slaveSocket);;
			double end = timer.elapsed();
			cout << "Start Time: " << start << ", end Time: " << end << endl;
			stats.addRequest(string(request), start, end);
			logger.log(slaveSocket, string(request));
			close(slaveSocket);
		}
		else if(concurrency == 1) {
			pid_t pid = fork();

			if(pid == 0) {
				Timer timer;
				double start = timer.elapsed();
				puts("Processing with thread");
				char * request = processTimeRequest(slaveSocket);;
				double end = timer.elapsed();
				cout << "Start Time: " << start << ", end Time: " << end << endl;
				stats.addRequest(string(request), start, end);
				logger.log(slaveSocket, string(request));
				exit(1);
			}
			else {
				waitpid(pid, NULL, 0);
				close(slaveSocket);
			}
			
		}
		else if(concurrency == 2) {
			pthread_t t;
			pthread_attr_t attr;

			pthread_attr_init(&attr);
			pthread_attr_setscope(&attr, PTHREAD_SCOPE_SYSTEM);

			pthread_create(&t, &attr, (void * (*)(void *))processTimeRequestThread, (void *)slaveSocket);
		}

	}
}
char * processTimeRequest(int socket) {
	// Buffer used to store the name received from the client
	
	puts("Processing request");
	const int maxNameLength = 1024;
	//int docLength = 0;
	int index = 0;			//index in currLine
	int n;
	unsigned char newChar;
	char* document_type = (char*)malloc(maxNameLength + 1);
	memset(document_type, '\0', maxNameLength + 1);
	char* requestName = (char*)malloc(maxNameLength + 1);
	memset(requestName, '\0', maxNameLength + 1);
	char currLine[maxNameLength + 1];
	char lastChar = 0;
	bool gotType = false;
	bool isDone = false;
	int lastLen = -1;
	while(n = read(socket, &newChar, sizeof(newChar)) && !isDone) {
		//printf("new:%d last:%d", newChar, lastChar);
		//printf("Read %d from client\n", n);
		printf("%c", newChar);
		if (newChar == '\n') {
			if (index == 2) {
				puts("END OF REQUEST");
				isDone = true;
				break;
			}
			//new line, process
			if (!gotType) {
				index++;
				currLine[index] = 0;	//null terminate
				document_type = getWordAtSpaceIndex(&currLine[0], 0);
				requestName = getWordAtSpaceIndex(&currLine[0], 1);
				printf("%s for %s\n", document_type, requestName);
				gotType = true;
			}
			//printf("last: %d, newlen: %d\n", lastLen, index);
			lastLen = index;
			index = 0;
			currLine[0] = 0;
		}
		currLine[index] = newChar;
		index++;
		lastChar = newChar;
	}
	//fprintf(stderr, "terminating at %d\n", length);
	//curr_string[length] = 0;
	if (strcmp(requestName, "/") == 0) {
		sender->sendFileNotFound(socket);
		return requestName;
	}
	else {
		fprintf(stderr, "strcmp returned: %d\n", strcmp(requestName, "/"));
	}

	fprintf(stderr, "document name: %s\n", requestName);
	char* ico = "/favicon.ico";
	char* secret = "11011";

	/*if (requestName == NULL) {
		fprintf(stderr, "Requested an invalid location\n");
		exit(0);
	}*/

	if(!strcmp(requestName, ico)) {
		memmove(requestName + strlen(secret), requestName, strlen(requestName) + 1);
		int i;
		for(i = 0; i < strlen(secret); i++) {
			requestName[i] = secret[i];
		}

		fprintf(stderr, "favico document name: %s\n", requestName);
	}

	puts("Checking now");
	char* token = strtok(requestName, "/");
	fprintf(stderr, "token: %s\n", token);
	if (token == NULL) {
		//this happens
		puts("Recieved a null token");
		sender->sendWrongSecret(socket);
		logger.log(socket, requestName);
		return requestName;
	}
	if(strcmp(token, secret)) {
		perror("incorrect secret key");
		sender->sendWrongSecret(socket);
		return requestName;
		//exit(0);
	}

	requestName = requestName + strlen(requestName) + 1;
	memmove(requestName + 1, requestName, strlen(requestName) + 1);
	requestName[0] = '/';
	
	//fprintf(stderr, "formatted name: %s\n\n", requestName);

	//if(strstr(requestName, "..") != 0) 
	//this doesn't work
	/*if (containsDots(requestName)) {
		fprintf(stderr, "contains ..\n");
		fprintf(stderr, "killing\n");
		exit(0);
	}	
	else {*/
		/*char path[maxNameLength + 1] = { 0 };
		char * r = realpath(requestName, path);

		if(r == NULL) {
			perror("path error");
			exit(0);
		}*/
	//}

	char currDir[256] = { 0 };
	getcwd(currDir, 256);

	if(!strncmp(requestName, "/htdocs", strlen("/htdocs"))
		|| !strncmp(requestName, "/icons", strlen("/icons"))
		|| !strncmp(requestName, "/templates", strlen("/templates"))
		|| !strncmp(requestName, "/cgi-bin", strlen("/cgi-bin"))) {
		strcat(currDir, "/http-root-dir/");
		strcat(currDir, requestName);
	}
	else {
		if (!strcmp(requestName, "/")) {
			strcat(currDir, "/http-root-dir/htdocs/index.html");
		}
		else if(!strcmp(requestName, "..")) {
			strcat(currDir, "/http-root-dir/");
		}
		else {
			strcat(currDir, "/http-root-dir/htdocs");
			strcat(currDir, requestName);
		}
	}
	/*Format Response*/

	if(strstr(requestName, ".html") != 0) {
		strcpy(document_type, "text/html");
	}
	else if(strstr(requestName, ".gif") != 0) {
		strcpy(document_type, "image/gif");
	}
	else if(strstr(requestName, ".jpg") != 0) {
		strcpy(document_type, "image/jpeg");
	}
	else {
		strcpy(document_type, "text/plain");
	}
	struct stat s;
	if (stat(currDir, &s) == 0 && s.st_mode & S_IFDIR) {
		puts("WE HAVE A DIRECTORY!");
		struct dirent *pDirent;
		DIR *pDir;
		pDir = opendir(currDir);
		if (pDir == NULL) {
			printf("Cannot open directory '%s'\n", currDir);
			sender->sendFileNotFound(socket);
			return requestName;
		}
		std::vector<FileInfo> files;
		while ((pDirent = readdir(pDir)) != NULL) {
			//printf("[%s]\n", pDirent->d_name);
			files.push_back(FileInfo(currDir, pDirent->d_name));
			//printf("Adding %s\n", pDirent->d_name);
		}
		/*puts("printing what we have");
		std::sort(files.begin(), files.end(), files[0].compare);
		files[0].print(files);*/
		closedir(pDir);
		sender->sendHtml(socket, files);
		return requestName;
	}
	if (strstr(requestName, "/cgi-bin") != NULL) {
		printf("WE GOT ME A BIN\n");
		CgiRunner runner;
		runner.run(socket, requestName, currDir);
		return requestName;
	}
	else if (strstr(requestName, "/stats") != NULL) {
		printf("It's like sportscenter here with all these stats\n");
		stats.handleGet(socket);
		return requestName;
	}
	puts("Opening file");
	FILE * file = fopen(currDir, "rb");
	if(file != NULL) {
		sender->sendFile(file, socket, document_type);
		return requestName;
	}
	else if (strstr(requestName, "/log") != NULL) {
		printf("Send ALL THE MEMORY\n");
		FILE * file = fopen(logger.getLocation().c_str(), "rb");
		if (file != NULL) {
			sender->sendFile(file, socket, document_type);
		}
		else {
			sender->sendEmpty(socket);
		}

		return requestName;
	}
	else {
		sender->sendFileNotFound(socket);
		return requestName;
	}
}

void processTimeRequestThread(int socket) {
	Timer timer;
	double start = timer.elapsed();
	puts("Processing with thread");
	char * request = processTimeRequest(socket);;
	double end = timer.elapsed();
	cout << "Start Time: " << start << ", end Time: " << end << endl;
	stats.addRequest(string(request), start, end);
	logger.log(socket, string(request));
	close(socket);
}

void threadsPool(int socket) {
	while(1) {
		pthread_mutex_lock(&mutex);

		struct sockaddr_in clientIPAddress;
		int alen = sizeof(clientIPAddress);
		int slaveSocket = accept(socket,
			(struct sockaddr *)&clientIPAddress,
			(socklen_t*)&alen);

		pthread_mutex_unlock(&mutex);

		processTimeRequest(slaveSocket);
		/*shutdown(slaveSocket, 1);
		close(slaveSocket);*/
	}
}
