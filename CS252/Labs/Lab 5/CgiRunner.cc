#include <stdio.h>
#include <unistd.h>
#include <string>
#include <iostream>
#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <arpa/inet.h>
#include <string.h>
#include <dlfcn.h>
#include <link.h>
#include <errno.h>
#include <sstream>
#include <vector>
#include "CgiRunner.hh"
#include "Sender.hh"
using namespace std;

typedef void(*httprunfunc)(int ssock, const char* querystring);

CgiRunner::CgiRunner() {}
int CgiRunner::locOfSlash(string line) {
	cout << "Called loc of slash" << endl;
	for (int i = 0; i < line.size(); i++) {
		if (line[i] == '/') {
			return i;
		}
	}
	return 0;
}
int CgiRunner::countArgs(char * line) {
	//counts occurences of '{'
	string dumb(line);
	int count = 0;
	for (int i = 0; i < dumb.size(); i++) {
		if (dumb[i] == '{') {
			count++;
		}
	}
	return count;
}
//Returns a string array from a vector of strings
char ** CgiRunner::toPrimitiveArray(vector<string> strings) {
	char ** arr = (char**)malloc(sizeof(char*) * strings.size());
	for (int i = 0; i < strings.size(); i++) {
		arr[i] = strdup(strings[i].c_str());
	}
	return arr;
}
//assume it's already properly formatted
char ** CgiRunner::resolveArguments(string line) {
	vector<string> arguments;
	for (int i = 0; i < line.size(); i++) {
		if (line[i] == '{') {
			string argument;
			for (int j = i + 1; j < line.size(); j++) {
				if (line[j] == '}') {
					i = j;
					break;
				}
				else {
					argument += line[j];
				}
			}
			arguments.push_back(argument);
		}
	}
	return toPrimitiveArray(arguments);
}
// /bin//sh becomes /bin/sh
char * CgiRunner::fixScriptPath(char * path) {
	string newPath;
	string oldPath(path);
	for (int i = 0; i < oldPath.length(); i++) {
		if (oldPath[i] == '/' && oldPath[i + 1] == '/') {
			continue;
		}
		newPath += oldPath[i];
	}
	char *  dupped = strdup(newPath.c_str());
	/*fprintf(stderr, "new path: %s\n", dupped);
	for (int i = strlen(dupped) - 3; i < strlen(dupped) + 1; i++) {
		fprintf(stderr, "%d ", dupped[i]);
	}
	fprintf(stderr, "checking null terminated\n");
	char blah[4] = { 'a','b','c',0 };
	for (int i = 0; i < strlen(blah) + 1; i++) {
		fprintf(stderr, "%d ", blah[i]);
	}*/
	return dupped;
}
string * CgiRunner::getProgram(string firstLine) {
	cout << "Called get program" << endl;
	int loc = locOfSlash(firstLine);
	cout << "slash at " << loc << " in " << firstLine << endl;
	string prog = firstLine.substr(loc, firstLine.size() - loc);
	string * result = new string();
	*result += prog;
	return result;
}
string toString(int num) {
	std::ostringstream stm;
	stm << num;
	return stm.str();
}
int getPort(int socket) {
	struct sockaddr_in sin;
	socklen_t len = sizeof(sin);
	if (getsockname(socket, (struct sockaddr *)&sin, &len) == -1)
		return 0;
	else
		return sin.sin_port;
}
int lastIndexOf(string s, char c) {
	int index = 0;
	for (int i = 0; i < s.length(); i++) {
		if (s[i] == c) {
			index = i;
		}
	}
	return index;
}
string getScriptName(string path) {
	return path.substr(lastIndexOf(path, '/'), path.length() - lastIndexOf(path, '/'));
}
void setvariables(string arguments, int socket, string path) {
	setenv("REQUEST_METHOD", "GET", 1);
	setenv("QUERY_STRING", arguments.c_str(), 1);
	setenv("SERVER_SOFTWARE", "myhttpd", 1);
	setenv("SERVER_NAME", "thed", 1);
	setenv("GATEWAY_INTERFACE", "", 1);
	setenv("SERVER_PROTOCOL", "HTTP/1.1", 1);
	setenv("SERVER_PORT", toString(getPort(socket)).c_str(), 1);
	setenv("SCRIPT_NAME", getScriptName(path).c_str(), 1);
	setenv("CONTENT_LENGTH", "0", 1);
}
void CgiRunner::runCgi(int socket, string firstLine, string path, string arguments) {
	string * program = getProgram(firstLine);
	if (path.find("jj") != string::npos) {
		program = &path;
	}
	cout << "Executing " << program->c_str() << " with " << path << endl;
	int ret = fork();
	if (ret == 0) {
		setvariables(arguments, socket, path);
		close(0);
		dup2(socket, STDOUT_FILENO);
		//dup2(socket, STDERR_FILENO);
		cout << "HTTP/1.1 200 Document\n\r";
		cout << "Server: MyServer/1.0\n\r";
		char  * toexecute = strdup(path.c_str());
		/*char const * arguments = (const char *)malloc(sizeof(char const) * path.size());
		arguments[0] = toexecute;*/
		char ** _arguments = (char**)malloc(sizeof(char*) * 3);
		if (firstLine == path) {
			_arguments[0] = strdup(path.c_str());
		}
		else {
			_arguments[0] = strdup(program->c_str());
		}
		_arguments[1] = fixScriptPath(toexecute);
		_arguments[2] = NULL;
		//cout << "Arguments: " << _arguments[0] << endl;
		if (execvp(_arguments[0], _arguments) == -1) {
			fprintf(stderr, "Could not execute _arguments[0] %s\n", _arguments[0]);
			fprintf(stderr, "Could not execute _arguments[1] %s\n", _arguments[1]);
			Sender sender;
			sender.sendCouldNotExecute(socket, _arguments[0], _arguments[1]);
			perror("execvp");
			exit(-1);
		}
	}
	else {
		//parent process
		waitpid(ret, NULL, 0);
		cout << "Closed socket after execution" << endl;
		close(socket);
	}
}
string * CgiRunner::readFirstLine(string fileToRead) {
	string * line = new string();
	FILE * file = fopen(fileToRead.c_str(), "rb");
	if (file != NULL) {
		char c;
		long l = 0;
		while (l = read(fileno(file), &c, 1)) {
			if (l == 0 || c == 0) {
				break;
			}
			if (c == '\n') {
				break;
			}
			printf("%d", c);
			*line += c;
		}
		fclose(file);
		if (line->size() == 0) {
			return NULL;
		}
		return line;
	}
	else {
		cout << "File doesn't exist: " << fileToRead << endl;
		return NULL;
	}
}
void CgiRunner::handleModule(int socket, string arguments, string resolvedpath) {
	// Opening 
	char * fixed = fixScriptPath(strdup(resolvedpath.c_str()));
	string dumb("");
	dumb += fixed;
	char * loc = strdup(dumb.c_str());
	void * lib = dlopen(loc, RTLD_LAZY);

	if (lib == NULL) {
		cout << "lib is null" << endl;
		fprintf(stderr, "%s not found\n", loc);
		perror("dlopen");
		Sender sender;
		sender.sendFileNotFound(socket);
		return;
	}
	/*int pid = fork();
	if (fork == 0) {*/
		// Get function to print hello
	cout << "executing module" << endl;
		httprunfunc hello_httprun;

		hello_httprun = (httprunfunc)dlsym(lib, "httprun");
		if (hello_httprun == NULL) {
			perror("dlsym: httprun not found:");
			Sender sender;
			sender.sendFileNotFound(socket);
			return;
		}
		write(socket, "HTTP/1.1 200 OK", 15);
		write(socket, "\r\n", 2);
		write(socket, "Server: MyServer/1.0", 20);
		write(socket, "\r\n", 2);
		// Call the function
		hello_httprun(socket, arguments.c_str());
	/*}
	else {
		waitpid(pid, NULL, 0);
		cout << "Ran module and joined with child" << endl;
	}*/
}
void CgiRunner::run(int socket, char * request, char * path) {
	cout << "request: " << request << ", path: " << path << endl;
	string resolvedpath;
	//char ** arguments;
	string arguments;
	//int argCount = 0;
	if (string(request).find("?") != string::npos) {
		cout << "has arguments" << endl;
		resolvedpath += string(path).substr(0, string(path).find("?"));
		//resolve arguments
		//argCount = countArgs(path);
		arguments = string(path).substr(string(path).find("?") + 1, string(path).size() - string(path).find("?"));
	}
	else {
		//argCount = 0;
		resolvedpath += string(path);
	}
	if (resolvedpath.find(".so") != string::npos) {
		cout << "It's a module script" << endl;
		handleModule(socket, arguments, resolvedpath);
		return;
		/*Sender sender;
		sender.sendFile(fopen(resolvedpath.c_str(), "rb"), socket, "text/plain");*/
	}
	string * line = readFirstLine(resolvedpath);
	if (line == NULL) {
		//assume it's an executable by itself
		runCgi(socket, resolvedpath, resolvedpath, arguments);
		return;
	}
	cout << "First line: " << line << endl;
	runCgi(socket, *line, resolvedpath, arguments);
}