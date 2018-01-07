#include <stdio.h>
#include <vector>
#include <string>
#include "FileInfo.hh"

#ifndef SENDER_H
#define SENDER_H
class Sender
{
public:
	Sender();
	void sendFileNotFound(int socket);
	void sendFile(FILE * file, int socket, char * document_type);
	void sendWrongSecret(int socket);
	void sendHtml(int socket, vector<FileInfo> files);
	void sendEmpty(int socket);
	void sendCouldNotExecute(int socket, char * program, char * script);
	void sendStats(int socket, string message);
private:
	void cleanup(int socket);
};
#endif