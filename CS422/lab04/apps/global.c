#include <stdio.h>
#include "../h/global.h"
#include <stdint.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <sys/time.h>
#include <string.h>
#include <stdlib.h>

uint32_t serialize(uint32_t value) {
    return htonl(value);
}
uint32_t deserialize(uint32_t value) {
    return ntohl(value);
}
uint32_t clientPayload() {
	return (uint32_t)1;
}
uint32_t serverPayload() {
	return (uint32_t)2;
}
int setup(char * port) {
	struct addrinfo hints, *results;
	int sock;

	// get host info, make socket, bind it to port 4950
	memset(&hints, 0, sizeof hints);
	hints.ai_family = AF_INET;  // use only IPv4
	hints.ai_socktype = SOCK_DGRAM;
	hints.ai_flags = AI_PASSIVE;
	getaddrinfo(NULL, port, &hints, &results);
	sock = socket(results->ai_family, results->ai_socktype, results->ai_protocol);
	if (sock < 0) {
		perror("socket");
		return -1;
	}
	//if (bind(sock, results->ai_addr, results->ai_addrlen) < 0) {
	struct sockaddr_in serverAddr;
	memset(&serverAddr, 0, sizeof(struct sockaddr_in));
	serverAddr.sin_family = AF_INET;
    serverAddr.sin_addr.s_addr = htonl(INADDR_ANY);
    serverAddr.sin_port = htons(atoi(port));
	//memset(serverAddr.sin_zero, 0, sizeof(serverAddr.sin_zero));
	if (bind(sock, (struct sockaddr *) &serverAddr, sizeof(serverAddr)) < 0) {
		perror("bind");
		return -1;
	}
	return sock;
}
//returns the time difference in microseconds
/*
struct timeval {
               time_t      tv_sec;     //seconds
               suseconds_t tv_usec;     //microseconds
           };
*/
int time_diff(struct timeval old, struct timeval current) {
	return ((current.tv_sec - old.tv_sec) * 1000000) +
		(current.tv_usec - old.tv_usec);
}