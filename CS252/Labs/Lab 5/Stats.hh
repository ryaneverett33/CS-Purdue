#include <string>
#include <pthread.h>
#include <time.h>
using namespace std;

#ifndef STATS_H
#define STATS_H
class Stats {
public:
	Stats();
	void addRequest(string url, double start, double end);
	void handleGet(int socket);
private:
	double calculateUptime();
	pthread_mutex_t lock;
	int requests;
	double minimumRequest;
	double maximumRequest;
	time_t startTime;
	string studentName;
	string toString(int num);
	string toString(double num);
	string longestRequest;
	string shortestRequest;
};
#endif