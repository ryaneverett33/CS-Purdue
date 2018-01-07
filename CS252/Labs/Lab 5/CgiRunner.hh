#include <string>
#include <vector>
using namespace std;
#ifndef CGIRUNNER_H
#define CGIRUNNER_H
class CgiRunner {
public:
	CgiRunner();
	void run(int socket, char * request, char * path);
private:
	int locOfSlash(string line);
	string * readFirstLine(string file);
	string * getProgram(string firstLine);
	void runCgi(int socket, string firstLine, string path, string arguments);
	//NOT USED
	char ** resolveArguments(string line);
	//NOT USED
	char ** toPrimitiveArray(vector<string> strings);
	//NOT USED
	int countArgs(char * line);
	char * fixScriptPath(char * script);
	void handleModule(int socket, string arguments, string resolvedPath);
};
#endif