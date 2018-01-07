using namespace std;
#include <dirent.h>
#include <time.h>
#include <string>
#include <vector>

#ifndef FILEINFO_H
#define FILEINFO_H
class FileInfo {
public:
	FileInfo(string name, int size, time_t modification);
	FileInfo(char * currentDirectory, char * name);
	string * format();			//formats as HTML table entry
	void print(vector<FileInfo> files);
	string name;
	int size;
	time_t modification;
	string fromTime(time_t time);
	static bool compare(FileInfo i, FileInfo j);
private:
	string toString(int a);
};
#endif