using namespace std;
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <string>
#include <iostream>
#include "HtmlMaker.hh"

string message;
HtmlMaker::HtmlMaker() {
	char currDir[256] = { 0 };
	getcwd(currDir, 256);
	strcat(currDir, "/http-root-dir/templates/directoryTop.html");
	FILE *file = fopen(currDir, "r");
	if (file == NULL) {
		cout << "Couldn't read the file" << endl << "Adding Basic template instead" << endl;
		message += "<html>\n";
		message += "<body>\n";
		message += "<table>\n";
		message += "<tr>\n";
		message += "<th>Name</th>\n";
		message += "<th>Size</th>\n";
		message += "<th>Modification Time</th>\n";
		message += "</tr>\n";
	}
	else {
		cout << "Reading from html template" << endl;
		int c;
		while ((c = getc(file)) != EOF) {
			message += c;
		}
		cout << "Loaded template" << endl; 
		fclose(file);
	}
	//In the future, read template from files
}
void HtmlMaker::addRow(string * row) {
	message += *row;
}
string HtmlMaker::c_str() {
	string result = message;
	result += makeEnd();
	/*char * str = (char*)malloc(sizeof(char) * result.length() + 1);
	for (int i = 0; i < result.length(); i++) {
		str[i] == result[i];
		cout << str[i];
	}
	str[result.length()] = 0;*/
	return result;
}
string HtmlMaker::makeEnd() {
	string end;
	end += "</table>\n";
	end += "</body>\n";
	end += "</html>";
	return end;
}