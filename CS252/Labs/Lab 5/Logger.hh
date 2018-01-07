#include <string>
#include <stdio.h>
using namespace std;
#ifndef LOGGER_H
#define LOGGER_H
class Logger {
public:
	Logger();
	void log(int socket, string request);
	void handleGet(int socket);
	string getLocation();
private:
	string getHost(int socket);
	pthread_mutex_t mLock;
	const char * fileLoc;
};
#endif