#include <string>
#include <stdlib.h>
#include <time.h>
#include <pthread.h>
#include <unistd.h>
#include <iostream>
#include <ctime>
#include <sstream>
#include "Stats.hh"
#include "Sender.hh"
using namespace std;

//for concurrency
pthread_mutex_t lock;
//count of all requests
int requests;
double minimumRequest;
string longestRequest;
double maximumRequest;
string shortestRequest;
//for calculating uptime
time_t startTime;
//name of student
string studentName;
Stats::Stats() {
	if (pthread_mutex_init(&lock, NULL) != 0) {
		perror("pthread_mutex_init");
	}
	minimumRequest = 0;
	maximumRequest = 0;
	shortestRequest = string("");
	longestRequest = string("");
	requests = 0;
	startTime = time(&startTime);
	studentName += "Ryan Everett";
}
void Stats::addRequest(string url, double start, double end) {
	if (url.length() == 0 || url.empty()) {
		return;
	}
	pthread_mutex_lock(&lock);
	double requestTime = end - start;
	if (requestTime < 0) {
		requestTime = requestTime * -1;
	}
	if (minimumRequest == 0 && maximumRequest == 0) {
		minimumRequest = requestTime;
		shortestRequest = url;
		maximumRequest = requestTime;
		longestRequest = url;
	}
	else {
		if (requestTime < minimumRequest) {
			minimumRequest = requestTime;
			shortestRequest = url;
		}
		else if (requestTime > maximumRequest) {
			maximumRequest = requestTime;
			longestRequest = url;
		}
	}
	requests++;
	pthread_mutex_unlock(&lock);
}
double Stats::calculateUptime() {
	time_t current;
	current = time(&current);
	return difftime(current, startTime);
}
string Stats::toString(int num) {
	std::ostringstream ss;
	ss << num;
	return ss.str();
}
string Stats::toString(double num) {
	std::ostringstream ss;
	ss << num;
	return ss.str();
}
void Stats::handleGet(int socket) {
	Sender sender;
	string message("<html>\n");
	message += "<body>\n";
	message += "<h4>Student Name: ";
	message += studentName;
	message += "</h4>\n";
	message += "<h4>Uptime in Seconds: ";
	message += toString(calculateUptime());
	message += "</h4>\n";
	message += "<h4>Number of request: ";
	message += toString(requests);
	message += "</h4>\n";
	message += "<h4>Longest request in MS: ";
	message += toString(maximumRequest);
	message += "</h4>\n";
	message += "<h4>Longest request: ";
	message += longestRequest;
	message += "</h4>\n";
	message += "<h4>Shortest request in MS: ";
	message += toString(minimumRequest);
	message += "</h4>\n";
	message += "<h4>Shortest request: ";
	message += shortestRequest;
	message += "</h4>\n";
	message += "</body>\n";
	message += "</html>";
	sender.sendStats(socket, message);
}