#include "command.hh"
#include <signal.h>
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <string.h>
int yyparse(void);

void call(int sig) {
	Command::_currentCommand.sighandle(sig);
}
void zombie(int sig) {
	Command::_currentCommand.zombie(sig);
}

int main(int argc, char ** argv) {
	//Setup signal intercepting
	
	struct sigaction sa;
    sa.sa_handler = call;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = SA_RESTART;

    if(sigaction(SIGINT, &sa, NULL)){
        perror("sigaction");
        exit(2);
    }
	
	struct sigaction sa2;
    sa2.sa_handler = zombie;
    sigemptyset(&sa2.sa_mask);
    sa2.sa_flags = SA_RESTART;

    if(sigaction(SIGCHLD, &sa2, NULL)){
        perror("sigaction");
        exit(2);
    }
	Command::_currentCommand.prompt();
	//Command::_currentCommand._shellLoc = strdup(argv[0]);
	yyparse();
}