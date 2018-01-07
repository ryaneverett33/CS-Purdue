#include <string>
#include <pthread.h>
#include <unistd.h>
#include <stdio.h>
#include <time.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <iostream>
#include "Logger.hh"
#include "Sender.hh"
using namespace std;

pthread_mutex_t mLock;
char * fileLoc;
Logger::Logger() {
	if (pthread_mutex_init(&mLock, NULL) != 0) {
		perror("pthread_mutex_init");
	}
	fileLoc = "access.log";
}
//Good ole Beej https://beej.us/guide/bgnet/output/html/multipage/getpeernameman.html
string Logger::getHost(int socket) {
	socklen_t len;
	struct sockaddr_storage addr;
	char ipstr[INET6_ADDRSTRLEN];
	int port;

	len = sizeof addr;
	getpeername(socket, (struct sockaddr*)&addr, &len);

	// deal with both IPv4 and IPv6:
	if (addr.ss_family == AF_INET) {
		struct sockaddr_in *s = (struct sockaddr_in *)&addr;
		port = ntohs(s->sin_port);
		inet_ntop(AF_INET, &s->sin_addr, ipstr, sizeof ipstr);
	}
	else { // AF_INET6
		struct sockaddr_in6 *s = (struct sockaddr_in6 *)&addr;
		port = ntohs(s->sin6_port);
		inet_ntop(AF_INET6, &s->sin6_addr, ipstr, sizeof ipstr);
	}
	return string(ipstr);
}
void Logger::log(int socket, string request) {
	pthread_mutex_lock(&mLock);
	FILE * file = fopen(fileLoc, "a");
	if (file == NULL) {
		perror("fopen");
		cout << "file loc: " << fileLoc << endl;
		return;
	}
	time_t rawtime;
	struct tm * timeinfo;
	char buffer[80];

	//get time
	time(&rawtime);
	timeinfo = localtime(&rawtime);
	strftime(buffer, sizeof(buffer), "%d-%m-%Y %I:%M:%S", timeinfo);
	std::string str(buffer);

	//get connecting host
	string host = getHost(socket);

	cout << "logging request" << endl;
	fprintf(file, "[%s] Host: %s\n", str.c_str(), host.c_str());
	fprintf(file, "[%s] Request: %s\n", str.c_str(), request.c_str());
	fflush(file);
	fclose(file);
	pthread_mutex_unlock(&mLock);
}
string Logger::getLocation() {
	return string(fileLoc);
}
//responds to /log
void Logger::handleGet(int socket) {

}