#include <stdlib.h>
int myprintf(const char* format, ...);

int main(int argc, char **argv) {
	//myprintf("%s %s\n", "hello", "world");
	myprintf("%d\n", 5);
	myprintf("%c\n", 'c');
	myprintf("%s %s\n", "hello", "world");
	myprintf("%x\n", 10);
	myprintf("%s %d\n", "-5 is", -5);
	myprintf("%d %s\n", -6, "is -6");
	myprintf("%d\n", 0);
	return 1;
}
