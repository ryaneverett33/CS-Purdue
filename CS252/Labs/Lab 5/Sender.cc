#include <stdio.h>
#include "Sender.hh"
#include <time.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <iostream>
#include <vector>
#include "FileInfo.hh"
#include "HtmlMaker.hh"

using namespace std;

Sender::Sender() {

}

void Sender::sendFileNotFound(int socket) {
	cout << "Sending 404" << endl;
	write(socket, "HTTP/1.1 404 File Not Found", 27);
	write(socket, "\r\n", 2);
	write(socket, "Server: thed/1.0", 20);
	write(socket, "\r\n", 2);
	write(socket, "Connection: close", 17);
	write(socket, "\r\n", 2);
	write(socket, "Content-Type: text/html", 23);
	write(socket, "\r\n\r\n", 4);
	write(socket, "File not found", 14);
	cleanup(socket);
}
void Sender::sendWrongSecret(int socket) {
	cout << "Sending wrong secret" << endl;
	write(socket, "HTTP/1.1 404 File Not Found", 27);
	write(socket, "\r\n", 2);
	write(socket, "Server: thed/1.0", 20);
	write(socket, "\r\n", 2);
	write(socket, "Connection: close", 17);
	write(socket, "\r\n", 2);
	write(socket, "Content-Type: text/html", 23);
	write(socket, "\r\n\r\n", 4);
	write(socket, "WRONG SECRET", 14);
	cleanup(socket);
}
void Sender::sendEmpty(int socket) {
	cout << "Sending wrong secret" << endl;
	write(socket, "HTTP/1.1 200 OK", 27);
	write(socket, "\r\n", 2);
	write(socket, "Server: thed/1.0", 20);
	write(socket, "\r\n", 2);
	write(socket, "Connection: close", 17);
	write(socket, "\r\n", 2);
	write(socket, "Content-Type: text/html", 23);
	write(socket, "\r\n\r\n", 4);
	cleanup(socket);
}
void Sender::sendCouldNotExecute(int socket, char * program, char * script) {
	//cout << "Sending could not execute" << endl;
	/*write(socket, "HTTP/1.1 404 File Not Found", 27);
	write(socket, "\r\n", 2);
	write(socket, "Server: MyServer/1.0", 20);
	write(socket, "\r\n", 2);*/
	write(socket, "Connection: close", 17);
	write(socket, "\r\n", 2);
	write(socket, "Content-Type: text/html", 23);
	write(socket, "\r\n\r\n", 4);
	write(socket, "Could not execute ", 18);
	write(socket, program, strlen(program));
	write(socket, " with script ", 14);
	write(socket, script, strlen(script));
}
void Sender::sendFile(FILE * file, int socket, char * document_type) {
	cout << "Sending file" << endl;
	/*Write success*/
	if (write(socket, "HTTP/1.1 200 OK", 15) == -1) {
		cout << "error" << endl;
	}
	if (write(socket, "\r\n", 2) == -1) {
		cout << "error" << endl;
	}
	if (write(socket, "Server: thed/1.0", 20) == -1) {
		cout << "error" << endl;
	}
	if (write(socket, "\r\n", 2) == -1) {
		cout << "error" << endl;
	}
	write(socket, "Connection: close", 17);
	write(socket, "\r\n", 2);
	if (write(socket, "Content-Type ", 13) == -1) {
		cout << "error" << endl;
	}
	if (write(socket, document_type, strlen(document_type) == -1)) {
		cout << "error" << endl;
	}
	if (write(socket, "\r\n\r\n", 4) == -1) {
		cout << "error" << endl;
	}

	char c;
	long l = 0;
	/*Write file data*/
	while (l = read(fileno(file), &c, sizeof(c))) {
		if (l != write(socket, &c, sizeof(c))) {
			cout << endl << endl << endl;
			perror("write error");
			cout << endl << endl << endl;
			return;
		}
	}
	//cleanup(socket);
	cout << "Closing file" << endl;
	fclose(file);
	cout << "returning from sendFile" << endl;
}
void Sender::sendHtml(int socket, vector<FileInfo> files) {
	HtmlMaker maker;
	for (int i = 0; i < files.size(); i++) {
		maker.addRow(files[i].format());
	}
	string message = maker.c_str();
	cout << "Sending Directory" << endl;
	//cout << "Sending message: " << message << endl;
	/*Write success*/
	write(socket, "HTTP/1.1 200 OK", 15);
	write(socket, "\r\n", 2);
	write(socket, "Server: thed/1.0", 20);
	write(socket, "\r\n", 2);
	write(socket, "Connection: close", 17);
	write(socket, "\r\n", 2);
	write(socket, "Content-Type: text/html", 23);
	write(socket, "\r\n\r\n", 4);
	write(socket, message.c_str(), message.length());
}
void Sender::sendStats(int socket, string message) {
	cout << "Sending Stats" << endl;
	//cout << "Sending message: " << message << endl;
	/*Write success*/
	write(socket, "HTTP/1.1 200 OK", 15);
	write(socket, "\r\n", 2);
	write(socket, "Server: thed/1.0", 20);
	write(socket, "\r\n", 2);
	write(socket, "Connection: close", 17);
	write(socket, "\r\n", 2);
	write(socket, "Content-Type: text/html", 23);
	write(socket, "\r\n\r\n", 4);
	write(socket, message.c_str(), message.length());
}
void Sender::cleanup(int socket) {
	cout << "called cleanup" << endl;
	//close(socket);
}