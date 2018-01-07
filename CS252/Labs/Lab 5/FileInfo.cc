#include <sys/stat.h>
#include "FileInfo.hh"
#include <iostream>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>
#include <sstream>
#include <vector>

using namespace std;

string name;
int size;
time_t modification;
FileInfo::FileInfo(string name, int size, time_t modification) {
	this->name = name;
	this->size = size;
	this->modification = modification;
}
FileInfo::FileInfo(char * currentDirectory, char * entryName) {
	struct stat st;
	char filename[512];
	snprintf(filename, sizeof(filename), "%s/%s", currentDirectory, entryName);
	lstat(filename, &st);
	this->name = string(entryName);
	this->modification = st.st_mtime;
	this->size = (int)st.st_size;
	//cout << this->name << endl;
}
string FileInfo::toString(int a) {
	std::ostringstream stm;
	stm << a;
	return stm.str();
}
//formats as HTML table entry
string * FileInfo::format() {
	string base("<tr>\n");
	string end("</tr>\n");
	string colBeginning("<td>");
	string colEnd("</td>");
	string formattedTime = fromTime(modification);
	//Name, Size, Date
	//<td>VALUE</td>
	/*char buffer1[colBeginning.length() + name.length() + colEnd.length() + 2];
	char buffer2[colBeginning.length() + 10 + colEnd.length() + 2];
	char buffer3[colBeginning.length() + formattedTime.length() + colEnd.length() + 2];
	sprintf(buffer1, "%s%s%s\n", colBeginning, name, colEnd);
	sprintf(buffer2, "%s%d%s\n", colBeginning, size, colEnd);
	sprintf(buffer3, "%s%s%s\n", colBeginning, formattedTime, colEnd);
	base = base + buffer1;
	base = base + buffer2;
	base = base + buffer3;
	base = base + end;/**/
	string * newer = new string();
	*newer += base;
	*newer += colBeginning;
	*newer += colEnd;
	*newer += colBeginning;
	*newer += name;
	*newer += colEnd;
	*newer += '\n';
	*newer += colBeginning;
	*newer += toString(size);
	*newer += colEnd;
	*newer += '\n';
	*newer += colBeginning;
	*newer += formattedTime;
	*newer += colEnd;
	*newer += '\n';
	*newer += end;
	return newer;
}
string FileInfo::fromTime(time_t time) {
	struct tm *info;
	char * buffer = (char*)malloc(sizeof(char) * 80);
	info = localtime(&time);
	strftime(buffer, 80, "%x - %I:%M%p", info);
	return buffer;
}
void FileInfo::print(vector<FileInfo> files) {
	cout << "file size: " << files.size() << endl;
	for (int i = 0; i < files.size(); i++) {
		FileInfo file = files[i];
		//printf("i: %d\n", i);
		//printf("name: %s\n", file.name.c_str());
		//printf("size: %d\n", file.size);
		//printf("modification: %s\n", fromTime(file.modification).c_str());
		printf("%s\n", file.format()->c_str());
		//printf("name: %s, size: %d, mod: %d", files[i].name.c_str(), files[i].size, (int)files[i].modification);
	}
}
bool FileInfo::compare(FileInfo i, FileInfo j) {
	return i.name < j.name;
}