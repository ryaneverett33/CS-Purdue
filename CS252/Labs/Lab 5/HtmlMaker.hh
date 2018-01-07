using namespace std;
#include <string>

#ifndef HTMLMAKER_H
#define HTMLMAKER_H
class HtmlMaker {
public:
	HtmlMaker();
	void addRow(string * row);
	string c_str();
	string message;
private:
	string makeEnd();
};
#endif