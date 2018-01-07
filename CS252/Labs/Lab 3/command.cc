/*
 * CS252: Shell project
 *
 * Template file.
 * You will need to add more code here to execute the command table.
 *
 * NOTE: You are responsible for fixing any bugs this code may have!
 *
 */

#include <cstdio>
#include <cstdlib>
#include <cstring>

#include <regex.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <signal.h>
#include <fcntl.h>

#include "command.hh"

void myunputc(int c);

bool executing = false;
int currentpid = -1;
int backpids[1000];

Command::Command()
{
	// Create available space for one simple command
	_numOfAvailableSimpleCommands = 1;
	_simpleCommands = (SimpleCommand **)
		malloc( _numOfSimpleCommands * sizeof( SimpleCommand * ) );

	_numOfSimpleCommands = 0;
	_outFile = 0;
	_inFile = 0;
	_errFile = 0;
	_background = 0;
}

bool regmatches(char *argument) {
	char * pattern = "\\${.*}";
	regex_t preg;
	regmatch_t match;
	
	if (regcomp(&preg, pattern, 0)) {
		perror("regex");
		exit(1);
	}
	//printf("compiled\n");
	//expand variable on match
	//can only expand environment variables
	if (!regexec(&preg, argument, 1, &match, 0)) {
		return true;
	}
	return false;
}

void Command::insertSimpleCommand( SimpleCommand * simpleCommand ) {
	if ( _numOfAvailableSimpleCommands == _numOfSimpleCommands ) {
		_numOfAvailableSimpleCommands *= 2;
		_simpleCommands = (SimpleCommand **) realloc( _simpleCommands,
			 _numOfAvailableSimpleCommands * sizeof( SimpleCommand * ) );
	}
	
	//check for 
	for (int i = 0; i < simpleCommand->_numOfArguments; i++) {
		if (regmatches(simpleCommand->_arguments[i])) {
			//puts("must expand");
			//printf("%s\n", simpleCommand->_arguments[i]);
			char * argument = simpleCommand->_arguments[i];
			char * variable = argument + 2; // move over ${
			int len = strlen(variable);
			variable[len - 1] = 0;
			char *tmp;
			if (strcmp(variable, "$") == 0) {
				//PID of shell process
				tmp = (char*)malloc(sizeof(char) * 6);
				//printf("current pid is: %d\n", getpid());
				sprintf(tmp, "%d", getpid());
			}
			else if (strcmp(variable, "?") == 0) {
				//return code of last executed simple command
				tmp = (char*)malloc(sizeof(char));
				sprintf(tmp, "%d", _lastCode);
			}
			else if (strcmp(variable, "!") == 0) {
				//PID of last process run in background
				if (_lastBackground == -1) {
					tmp = strdup("");
				}
				//if {
					tmp = (char*)malloc(sizeof(char) * 6);
					sprintf(tmp, "%d", _lastBackground);
				//}
			}
			else if (strcmp(variable, "_") == 0) {
				//last argument in the previous command
				tmp = _lastArgument;
			}
			else if (strcmp(variable, "SHELL") == 0) {
				//the path of the executable
				tmp = _shellLoc;
			}
			
			else {
				tmp = strdup(getenv(variable));
			}
			simpleCommand->_arguments[i] = tmp;
			//printf("Expanded to %s and %s\n", variable, tmp);
		}
		//printf("%s\n", simpleCommand->_arguments[i]);
	}
	
	_simpleCommands[ _numOfSimpleCommands ] = simpleCommand;
	_numOfSimpleCommands++;
}

void Command:: clear() {
	for ( int i = 0; i < _numOfSimpleCommands; i++ ) {
		for ( int j = 0; j < _simpleCommands[ i ]->_numOfArguments; j ++ ) {
			free ( _simpleCommands[ i ]->_arguments[ j ] );
		}
		
		free ( _simpleCommands[ i ]->_arguments );
		free ( _simpleCommands[ i ] );
	}

	if ( _outFile ) {
		free( _outFile );
	}

	if ( _inFile ) {
		free( _inFile );
	}

	if ( _errFile ) {
		free( _errFile );
	}

	_numOfSimpleCommands = 0;
	_outFile = 0;
	_inFile = 0;
	_errFile = 0;
	_background = 0;
}

void Command::print() {
	printf("\n\n");
	printf("              COMMAND TABLE                \n");
	printf("\n");
	printf("  #   Simple Commands\n");
	printf("  --- ----------------------------------------------------------\n");
	
	for ( int i = 0; i < _numOfSimpleCommands; i++ ) {
		printf("  %-3d ", i );
		for ( int j = 0; j < _simpleCommands[i]->_numOfArguments; j++ ) {
			printf("\"%s\" \t", _simpleCommands[i]->_arguments[ j ] );
		}
	}

	printf( "\n\n" );
	printf( "  Output       Input        Error        Background\n" );
	printf( "  ------------ ------------ ------------ ------------\n" );
	printf( "  %-12s %-12s %-12s %-12s\n", _outFile?_outFile:"default",
		_inFile?_inFile:"default", _errFile?_errFile:"default",
		_background?"YES":"NO");
	printf( "\n\n" );
	
}
char * getKey(char * envbit) {
	//find the index of =
	int i = 0;
	int index = -1;
	while (envbit[i] != 0) {
		if (envbit[i] == '=') {
			index = i;
		}
		i = i + 1;
	}
	if (index == -1) {
		//didn't find it
		return NULL;
	}
	//printf("= is at %d\n", index);
	char * substr = (char*)malloc(sizeof(char) * index + 1);
	strncpy(substr, envbit, index);
	substr[index] = 0;
	return substr;
}
char * getHomeDir() {
	char** env = environ;
	int i = 0;
	while (env[i] != NULL) {
		char * key = getKey(env[i]);
		//printf("%s\n", key);
		if (strcmp(key, "HOME") == 0) {
			//puts("found home");
			char * tokens = strtok(env[i], "=");
			int j = 0;
			while (tokens != NULL) {
				if (j == 1) {
					//printf("Home: %s\n", tokens);
					return tokens;
				}
				j = j + 1;
				tokens = strtok(NULL, "=");
			}
		}
		i = i + 1;
	}
	return NULL;
}
void cleanCommand(SimpleCommand* command) {
	if (command == NULL) {
		return;
	}
	for (int j = 0; j < command->_numOfArguments; j++) { 
		char* argument = command->_arguments[j];
		//printf("%s\n", argument);
		//check if line has wildcard
		int k = 0;
		bool hasWild = false;
		char* args = argument;
		/*while (args != NULL) {
			if (*args == '*') {
				hasWild = true;
				break;
			}
			args++;
		}*/
		while (args[k] != 0) {
			if (args[k] == '*') {
				hasWild = true;
				break;
			}
			k++;
		}
		if (hasWild) {
			//printf("Has a wildcard: %s\n", argument);
			//remove at location j
			command->_numOfArguments--;
			char **newset = (char**)malloc(sizeof(char*) * command->_numOfArguments);
			for (int x = 0; x < command->_numOfArguments; x++) {
				newset[x] = (char*)malloc(sizeof(char) * strlen(command->_arguments[x]));
				newset[x] = strdup(command->_arguments[x]);
			}
			free(command->_arguments);
			command->_arguments = newset;
			
		}
		if (strlen(argument) == 0) {
			break;
		}
		else {
			//printf("len: %d\n", strlen(argument));
		}
	}
}
void printArgs() {
	Command curr = Command::_currentCommand;
	for (int i = 0; i < curr._numOfAvailableSimpleCommands; i++) {
		SimpleCommand* command = curr._simpleCommands[i];
		for (int j = 0; j < command->_numOfArguments; j++) {
			printf("%d-%d %s\n", i, j, command->_arguments[j]);
		}
	}
}
void Command::storeLastArgument(SimpleCommand* command) {
	_lastArgument = strdup(command->_arguments[command->_numOfArguments - 1]);
}

void Command::execute() {
	// Don't do anything if there are no simple commands
	if ( _numOfSimpleCommands == 0) {
		prompt();
		return;
	}
	
	if (strcmp(_simpleCommands[0]->_arguments[0], "exit") == 0 || strcmp(_simpleCommands[0]->_arguments[0], "quit") == 0) {
		if (isatty(0)) {
			printf("\nGoodbye!\n\n");
			exit(1);
		}
	}
	
	executing = true;
	// Print contents of Command data structure
	//if (isatty(0)) { print(); }
	//if (isatty(0)) { print(); }
	//save stdin, stdout, stderr
	int tmpin = dup(0);
	int tmpout = dup(1);
	int tmperr = dup(2);

	// Add execution here
	int fdin;			//in descriptor during execution
	int fdout;		//out descriptor
	//int fderr;
	
	if (_inFile) {
		fdin = open(_inFile, O_RDONLY);
	}
	else {
		fdin = dup(tmpin);
	}
	/*if (_errFile) {
		fderr = open(_errFile, O_RDONLY);
	}
	else {
		//fderr = dup(tmperr);
	}*/
	int ret;
	// For every simple command fork a new process
	// Setup i/o redirection
	// and call exec
	if (strcmp(_simpleCommands[0]->_arguments[0], "exit") == 0 || strcmp(_simpleCommands[0]->_arguments[0], "quit") == 0) {
		if (isatty(0)) {
			printf("\nGoodbye!\n\n");
			dup2(tmpin, 0);
			dup2(tmpout, 1);
			dup2(tmperr, 2);
			close(tmpin);
			close(tmpout);
			close(tmperr);
			exit(1);
		}
	}
	
	for (int i = 0; i < _numOfSimpleCommands; i++) {
		//redirect the stdin/stdout
		//printf("Executing %d\n", )
		dup2(fdin, 0);
		close(fdin);
		SimpleCommand* command = _simpleCommands[i];
		//cleanCommand(command);
		//printArgs();
		if (i == _numOfSimpleCommands - 1) {
			storeLastArgument(command);
			//last command
			if (_outFile && _outAppend) {
				fdout = open(_outFile, O_WRONLY | O_CREAT | O_APPEND , 0666);
			}
			else if (_outFile) {
				fdout = open(_outFile, O_WRONLY | O_CREAT | O_TRUNC, 0666);
			}
			else {
				fdout = dup(tmpout);
			}
			
			/*if (_errFile && !_errAppend) {
				fderr = open(_errFile, O_WRONLY | O_CREAT , 0666 );
			}
			else if (_errFile && _errAppend) {
				//fprintf(stdout, "Appending to err\n");
				fderr = open(_errFile, O_WRONLY | O_CREAT | O_APPEND, 0666 );
			}
			else {
				fderr = dup(tmperr);
			}*/
		}
		else {
			//pipe everything
			int fdpipe[2];
			pipe(fdpipe);
			fdout = fdpipe[1];
			fdin = fdpipe[0];
			//dup2(fdpipe[1], 1);
			//close(fdpipe[1]);
		}
		
		dup2(fdout, 1);
		//close(fdout);
		//Redirect output
		if (_errFile) {
			dup2(fdout, 2);
			
		}
		close(fdout);
		//close(fderr);
		//fprintf(stderr, "Forking\n");
		if (strcmp(_simpleCommands[i]->_arguments[0], "setenv") == 0) {
			//do things
			if (_simpleCommands[i]->_numOfArguments < 3) {
				//print error
				printf("Usage: setenv NAME VALUE\n");
				break;
			}
			
			if (setenv(_simpleCommands[i]->_arguments[1], _simpleCommands[i]->_arguments[2], 1) != 0) {
				perror("setenv");
			}
			else {
				if (strcmp(_simpleCommands[i]->_arguments[1], "PROMPT") == 0) {
					_shellName = (char*)malloc(sizeof(char) * strlen(_simpleCommands[i]->_arguments[2]) + 1);
					printf("arg2: %s\n", _simpleCommands[i]->_arguments[2]);
					strcpy(_simpleCommands[i]->_arguments[2], _shellName);
				}
			}
		}
		else if (strcmp(_simpleCommands[i]->_arguments[0], "unsetenv") == 0) {
			if (_simpleCommands[i]->_numOfArguments < 2) {
				//print error
				printf("Usage: unsetenv NAME \n");
				break;
			}
			//do things
			if (unsetenv(_simpleCommands[i]->_arguments[1]) != 0) {
				perror("unsetenv");
			}
		}
		else if (strcmp(_simpleCommands[i]->_arguments[0], "cd") == 0) {
			if (_simpleCommands[i]->_numOfArguments < 2) {
				//change directory to home
				//puts("Getting home");
				char * home = getHomeDir();
				if (home != NULL) {
					if (chdir(home) != 0) {
						perror("chdir");
					}
				}
				//things went horribly wrong
			}
			else {
				//change to supplied
				if (chdir(_simpleCommands[i]->_arguments[1]) != 0) {
					perror("chdir");
				}
			}
			//do things
		}
		else if (strcmp(_simpleCommands[i]->_arguments[0], "jobs") == 0) {
			//do things

		}
		else if (strcmp(_simpleCommands[0]->_arguments[0], "source") == 0) {
			if (_simpleCommands[0]->_numOfArguments < 2) {
				//print error
				printf("Usage: source FILE \n");
				//break;
			}
			//read file character by character
			char buffer[1000];
			int i = 0;
			char c;
			//do things
			int file = open(_simpleCommands[0]->_arguments[1], NULL);
			while (read(file, &c, 1)) {
				if (c == '\n') {
					//printf("NEWLINE\n");
					buffer[i] = 0;
					i = i + 1;
					//printf("Unputting with i=%d\n", i);
					int j;
					for (j = i; j > -1; j--) {
						//printf("unput loop\n");
						//printf("%c", buffer[j]);
						myunputc(buffer[j]);
					}
				}
				else {
					//printf("%c", c);
					buffer[i] = c;
					i++;
				}
			}
			//myunputc(0);
			close(file);
			//_isSource = true;
			//flush stdout
			//fflush(stdout);
			//clear();
			//printf("\n");
		}
		else if (strcmp(_simpleCommands[i]->_arguments[0], "fg") == 0) {
			if (_simpleCommands[i]->_numOfArguments < 2) {
				//print error
				printf("Usage: fg PID \n");
			}
			//do things
		}
		else if (strcmp(_simpleCommands[i]->_arguments[0], "bg") == 0) {
			if (_simpleCommands[i]->_numOfArguments < 2) {
				//print error
				printf("Usage: bg PID \n");
			}
			//do things
		}
		else {
			ret = fork();
			if (ret == 0) {
				//execute this new command
				//execvp(file location, arguments array)
				//fprintf(stderr, "Command: %s\n", command->_arguments[0]);
				if (strcmp(_simpleCommands[i]->_arguments[0], "printenv") == 0) {
					//do things
					//apparently pexec(env) does the same
					char** env = environ;
					int i = 0;
					while (env[i] != NULL) {
						fprintf(stdout, "%s\n", env[i]);
						i = i + 1;
					}
					exit(0);
				}
				execvp(command->_arguments[0], command->_arguments);
				perror("execvp");
				exit(1);
			}
		}
		/*else {
			perror("fork");
		}*/
	}
	//restore in/out defaults
	dup2(tmpin, 0);
	dup2(tmpout, 1);
	dup2(tmperr, 2);
	close(tmpin);
	close(tmpout);
	close(tmperr);
	
	//wait for the last pid to complete
	if (!_background) {
		currentpid = ret;
		waitpid(ret, NULL, 0);
	}
	else {
		//add to background list
		int i = 0;
		for (i = 0; i < 1000; i++) {
			if (backpids[i] == 0) {
				break;
			}
		}
		//printf("Added %d at %d\n", ret, i); 
		backpids[i] = ret;
	}
	currentpid = -1;
	executing = false;
	// Print new prompt
	//if (_outFile) {
	//	exit(1);
	//	printf("\n");
	//}
	//else {
		// Clear to prepare for next command
		if (!_isSource){
			prompt();
			clear();
		}
		else {
			myunputc(10);
			clear();
			_isSource = false;
		}
	//}
}

// Shell implementation

void Command::prompt() {
	if (isatty(0)) {
		if (_shellName != NULL) {
			char* value;
			value = getenv("PROMPT");
			printf("%s", value);
		}
		else {
			printf("myshell>");
		}
		fflush(stdout);
	}
	if (_shellPid == -1) _shellPid = (int)getpid();
}
//ONLY FOR CTRL-C
void Command::sighandle(int sig) {
	//fprintf(stderr, "Got signal: %d\n", sig);
	//Ctrl-C
	if (sig == 2) {
		if (executing) {
			//kill currently running process
			if (currentpid != -1) {
				//send signal
				kill(currentpid, sig);
				printf("\n");
			}
			else {
				printf("Current pid is -1\n");
			}
		}
		else {
			printf("\n");
			clear();
			prompt();
		}
	}
}
void Command::zombie(int sig) {
	//printf("Recieved %d\n", sig);
	int pid = wait3(0,0, NULL);
	//blocking wait
	while (waitpid(-1, NULL, WNOHANG) > 0) {
		//do nothing;
	}
	//printf("%d changed\n", pid);
	bool foundit = false;
	for (int i = 0; i < 1000; i++) {
		if (backpids[i] == pid) {
			//printf("Found at %d\n", i);
			foundit = true;
		}
	}
	if (foundit) {
		//printf("[%d] exited\n", pid);
		Command::_currentCommand.prompt();
	}
}

Command Command::_currentCommand;
SimpleCommand * Command::_currentSimpleCommand;
