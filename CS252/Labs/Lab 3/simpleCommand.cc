#include <cstdlib>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <regex.h>
#include <unistd.h>
#include <pwd.h>

#include "simpleCommand.hh"

bool containsWild(char* line) {
	int i = 0;
	while (line[i] != 0) {
		if (line[i] == '*') {
			return true;
		}
		i++;
	}
	return false;
}

SimpleCommand::SimpleCommand() {
	// Create available space for 5 arguments
	_numOfAvailableArguments = 5;
	_numOfArguments = 0;
	_arguments = (char **) malloc( _numOfAvailableArguments * sizeof( char * ) );
}
 
void SimpleCommand::insertArgument( char * argument ) {
	if (argument[0] == '*' || containsWild(argument)) {
		return;
	}
	if ( _numOfAvailableArguments == _numOfArguments  + 1 ) {
		// Double the available space
		_numOfAvailableArguments *= 2;
		_arguments = (char **) realloc( _arguments,
				  _numOfAvailableArguments * sizeof( char * ) );
	}
	
	//char * pattern = "(\$\{[^ \t\n]*\})";
	char * pattern = "\\${.*}";
	regex_t preg;
	regmatch_t match;
	
	if (regcomp(&preg, pattern, 0)) {
		perror("regex");
		exit(1);
	}
	
	//expand variable on match
	//can only expand environment variables
	/*if (!regexec(&preg, argument, 1, &match, 0) && strlen(argument) > 3) {
		char * variable = argument + 2; // move over ${
		int len = strlen(argument);
		variable[len - 2 - 1] = 0;
		//printf("Putting %s, len = %d\n", variable, len);
		//get the variable
		//char** env = environ;
		//int i = 0;
		//char *token;
		char *result = NULL;
		/*while (env[i] != NULL) {
			//fprintf(stdout, "%s\n", env[i]);
			token = strtok(env[i], "=");
			if (strcmp(token, variable) == 0) {
				token = strtok(env[i], "=");
				token = strtok(env[i], "=");
				printf("token length: %d\n", strlen(token));
				printf("token: %s\n", token);
				result = (char*)malloc(sizeof(char) * strlen(token));
				strcpy(result, token);
			}
			i = i + 1;
		}*/
		/*char * tmp = NULL;
		tmp = getenv(variable);
		if (tmp == NULL) {
			result = (char*)malloc(sizeof(char));
			result[0] = 0;
		}
		else {
			result = (char*)malloc(sizeof(char) * strlen(tmp) + 1);
			strcpy(result, tmp);
			result[strlen(tmp)] = 0;
		}
		//printf("result: %s\n", result);
		_arguments[ _numOfArguments ] = result;
		

		// Add NULL argument at the end
		_arguments[ _numOfArguments + 1] = NULL;
		
		_numOfArguments++;
		//printf("leaving\n");
	}*/
	if (argument[0] == '~') {
		if (strlen(argument) == 1) {
			struct passwd *passw = getpwuid(getuid());
			char *home = passw->pw_dir;
			
			char * newarg = (char*)malloc((strlen(home) + strlen(argument)) * sizeof(char) + 1);
			newarg[0] = '\0';
			//Adds home directory '/' and the argument together
			strcat( newarg, home );
			strcat( newarg, "/" );
			strcat( newarg, (char *)(argument + 1) );
			newarg[strlen(home) + strlen(argument) + 1] = 0;
			
			//printf("Expanded: %s\n", newarg);
			argument = newarg;
		}
		else {
			struct passwd *passw = getpwnam(argument+1);
			if (passw == NULL) {
				//printf("fucking null\n");
				//just fucking add "/homes/" + whatever
				char * directory = argument + 1;		//get rid of tilde
				char * expanded = (char*)malloc((strlen(directory) + strlen("/homes/") + 1) * sizeof(char));
				strcat(expanded, "/homes/");
				strcat(expanded, directory);
				expanded[strlen(directory) + strlen("/homes/")] = 0;
				argument = expanded;
			}
			else {
				argument = strdup(passw->pw_dir);
			}
		}
		
		_arguments[ _numOfArguments ] = argument;
		

		// Add NULL argument at the end
		_arguments[ _numOfArguments + 1] = NULL;
		
		_numOfArguments++;
		//printf("Stored as: %s\n", _arguments[ _numOfArguments ]);
		//printf("leaving\n");
		
	}
	else {
		_arguments[ _numOfArguments ] = argument;

		// Add NULL argument at the end
		_arguments[ _numOfArguments + 1] = NULL;
		
		_numOfArguments++;
	}
}
