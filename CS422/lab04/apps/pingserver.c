#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <sys/time.h>
#include <netdb.h>
#include <errno.h>
#include <unistd.h>
#include "../h/global.h"

//return listening socket
/*int setup(char * port) {
	struct addrinfo hints, *results;
	int sock;

	// get host info, make socket, bind it to port 4950
	memset(&hints, 0, sizeof hints);
	hints.ai_family = AF_UNSPEC;  // use IPv4 or IPv6, whichever
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
    serverAddr.sin_port = htons(50008);
	//memset(serverAddr.sin_zero, 0, sizeof(serverAddr.sin_zero));
	if (bind(sock, (struct sockaddr *) &serverAddr, sizeof(serverAddr)) < 0) {
		perror("bind");
		return -1;
	}
	return sock;
}*/
struct sockaddr * makeConnect(struct sockaddr_in sender) {
	struct sockaddr_in * serverAddr = (struct sockaddr_in *)malloc(sizeof(struct sockaddr_in));
        memset(serverAddr, 0, sizeof(*serverAddr));
        serverAddr->sin_family = AF_INET;
        serverAddr->sin_addr.s_addr = sender.sin_addr.s_addr;
        serverAddr->sin_port = sender.sin_port;
	return (struct sockaddr*)serverAddr;
}

int main(int argc, char *argv[])
{
	char * port;
	int awake_time;
	int sleep_time;
	//struct timeval awake_time_period;
	//struct timeval * t1, t2;
	//epoch is in seconds
	if (argc < 4) {
		printf("USAGE: application_number  awake_period_in_seconds  sleep_period_in_seconds\n");
		return -1;
	}
	port = argv[1];
	awake_time = atoi(argv[2]);
	if (awake_time < 0) {
		awake_time = 0;		//always awake
	}
	sleep_time = atoi(argv[3]);
	if (sleep_time < 0) {
		sleep_time = 0;		//no sleep
	}

	int sock = setup(port);
	if (sock <= 0) {
		printf("Failed to bind, quitting\n");
		return -1;
	}
	struct timeval awake_time_period = { awake_time, 0};

	//gettimeofday(&awake_time_period, NULL);
	//awake_time_period.tv_sec += awake_time;

	while(1)
	{
		setsockopt(sock, SOL_SOCKET, SO_RCVTIMEO, (struct timeval *)&awake_time_period, sizeof(struct timeval));
		struct sockaddr_in address;
		//uint32_t data;
		uint32_t buffer;
		socklen_t len = sizeof(address);
		//if(recvfrom(socket_fd, buffer, 2, 0, (struct sockaddr*)&dest_addr, &len) == -1)
		int recieved = recvfrom(sock, (void*)&buffer, sizeof(buffer), 0, (struct sockaddr *)&address, &len);
		if (recieved <= 0) {
			if (errno == EAGAIN || errno == EWOULDBLOCK) {
				//printf("timed out\n");
				//printf("Sleeping for %d seconds\n", sleep_time);
				sleep(sleep_time);
				continue;
			}
			//perror("recvfrom");
			//printf("got nothing %d\n", recieved);
		}
		else {
			//printf("recieved %d bytes, buffer: %d\n", recieved, buffer);
			struct sockaddr * responder = makeConnect(address);
			uint32_t payload = serverPayload();
			int sent = sendto(sock, (void*)&payload, 4, 0, (struct sockaddr *)responder, sizeof(*responder));
			
			if (sent == -1)
				perror("sendto");
			//printf("Sent %d\n", sent);

			//printf("recieved %d bytes, value: %d\n", recieved, deserialize(data));
		}
	
	}

	return 0;

}
