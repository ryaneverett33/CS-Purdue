#include <stdio.h>
#include <stdlib.h>
#include <netdb.h>
#include <string.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <stdint.h>
#include <sys/time.h>
#include "../h/global.h"

struct host_table_entry * host_table[MAX_NUM_HOSTS];
int hostCount = 0;
char * port;

char * getIpAddress(char * hostname) {
	//assume ipv4 -> 255.255.255.255
	char * string = (char*)malloc(sizeof(char) * 16);
	struct hostent * host;
    struct in_addr ** list;		//array of addresses

	host = gethostbyname(hostname);
	if (host == NULL) {
		return NULL;
	}
	list = (struct in_addr **) host->h_addr_list;
	int i = 0;
	while(list[i] != NULL) {
		strcpy(string, inet_ntoa(*(list[i])));
		i++;
	}
	return string;
}
char * getRawIpAddress(struct sockaddr_in * rawAddress) {
	//struct sockaddr * lameSockAddress = (struct sockaddr *)rawAddress;
	char * string = (char*)malloc(sizeof(char) * 16);
	inet_ntop(rawAddress->sin_family, &(rawAddress->sin_addr), string, 16);
	return string;
}
struct host_table_entry * resolveEntry(char * hostname) {
	//printf("ip address for %s is %s\n", hostname, getIpAddress(hostname));
	struct host_table_entry * entry = (struct host_table_entry *)malloc(sizeof(struct host_table_entry));
	entry->hostname = hostname;
	entry->ip_addr = getIpAddress(hostname);
	if (entry->ip_addr == NULL) {
		free(entry);
		return NULL;
	}
	return entry;
}
//return socket for sending
/*int setupC(char * hostname, char * port) {
	struct addrinfo hints;
	struct addrinfo * results;
	int sock;

	memset(&hints, 0, sizeof hints);
	hints.ai_family = AF_INET;
	hints.ai_socktype = SOCK_DGRAM;
	if (getaddrinfo(hostname, port, &hints, &results) < 0)
		perror("getaddrinfo");

	//Make the socket and connect to the server, return fd
	sock = socket(results->ai_family, results->ai_socktype, results->ai_protocol);
	if (sock == -1) {
		perror("socket");
		return -1;
	}
	return sock;
}*/
//get current timestamp
struct timeval timestamp() {
	struct timeval currenttime;
	gettimeofday(&currenttime, NULL);
	return currenttime;
}
struct sockaddr_in * makeConnectC(struct host_table_entry * entry) {
	struct sockaddr_in * serverAddr = (struct sockaddr_in *)malloc(sizeof(struct sockaddr_in));
        memset(serverAddr, 0, sizeof(*serverAddr));
        serverAddr->sin_family = AF_INET;
        serverAddr->sin_addr.s_addr = inet_addr(entry->ip_addr);
        serverAddr->sin_port = htons(atoi(port));
	return serverAddr;
}
struct host_table_entry * getEntrant(char * ip_addr) {
	if (ip_addr == NULL) {
		return NULL;
	}
	int i = 0;
	for (i = 0; i < hostCount; i++) {
		struct host_table_entry * entry = host_table[i];
		if (entry != NULL) {
			if (strcmp(entry->ip_addr, ip_addr) == 0) {
				//found it!
				return entry;
			}
		}
	}
	return NULL;
}

int main(int argc, char *argv[]){
	//printf("current time is %lu\n", timestamp().tv_usec);
	if (argc < 3) {
		printf("USAGE: application_number  hostname1_to_ping  hostname2_to_ping  hostname3_to_ping ...\n");
		return -1;
	}
	else {
		port = argv[1];
		int i = 0;
		for (i = 2; i < argc; i++) {
			struct host_table_entry * entry = resolveEntry(argv[i]);
			if (entry != NULL) {
				host_table[hostCount] = entry;
				hostCount++;
				//printf("Added host (%s/%s) to host table\n", entry->hostname, entry->ip_addr);
			}
		}
	}
	
	int i = 0;
	//int sock = setupC(NULL, port);
	int sock = setup(port);
	for (i = 0; i < hostCount; i++) {
		struct host_table_entry * entry = host_table[i];
		//sock = setupC(entry->hostname, port);
		//printf("Socket is: %d\n", sock);

		struct sockaddr_in * serverAddr = makeConnectC(entry);
		uint32_t payload = clientPayload();
		//payload = serialize(payload);

		entry->timestamp = timestamp();
		host_table[i] = entry;
		int sent = sendto(sock, (void*)&payload, 4, 0, (struct sockaddr *)serverAddr, sizeof(*serverAddr));
		if (sent == -1)
			perror("sendto");
		//printf("Sent %d\n", sent);
	}
	for (i = 0; i < hostCount; i++) {
		uint32_t buffer;

		struct sockaddr_in address;
		socklen_t len = sizeof(address);
		int recieved = recvfrom(sock, (void*)&buffer, sizeof(buffer), 0, (struct sockaddr *)&address, &len);


		if (recieved <= 0) {
			perror("recvfrom");
			//printf("got nothing %d\n", recieved);
		}
		else {
			//buffer = deserialize(buffer);
			//printf("recieved %d bytes, buffer: %d where: %s\n", recieved, buffer, getRawIpAddress(&address));
			struct host_table_entry * responder = getEntrant(getRawIpAddress(&address));
			if (responder == NULL) {
				printf("Failed to get entry for %s\n", getRawIpAddress(&address));
			}
			else {
				printf("Reply from server %s, latency : %dusec\n", responder->ip_addr, time_diff(responder->timestamp, timestamp()));
			}

			//printf("recieved %d bytes, value: %d\n", recieved, deserialize(data));
		}
	}

	return 0;

}
