
/*
 * CS-252
 * shell.y: parser for shell
 *
 * This parser compiles the following grammar:
 *
 *	cmd [arg]* [> filename]
 *
 * you must extend it to understand the complete shell grammar
 *
 */

%code requires 
{
#include <string>

#if __cplusplus > 199711L
#define register      // Deprecated in C++11 so remove the keyword
#endif
}

%union
{
  char        *string_val;
  // Example of using a c++ type in yacc
  std::string *cpp_string;
}

%token <string_val> WORD
%token NOTOKEN GREAT NEWLINE GREATGREAT GREATAMPERSAND GREATGREATAMPERSAND LESS PIPE AMPERSAND TWOGREAT WEIRDGREAT
%{
//#define yylex yylex
#include <cstdio>
#include <string.h>
#include <fcntl.h>
#include <regex.h>
#include <unistd.h>
#include <dirent.h>
#include <fcntl.h>
#include "command.hh"

void yyerror(const char * s);
int yylex();

int argindex;
bool hasWildcard(char* line) {
	/*char *a = line;
	while (a != NULL) {
		if (*a == '*') {
			//puts("has wildcard");
			return true;
		}
		a++;
	}*/
	int i = 0;
	while (line[i] != 0) {
		if (line[i] == '*') {
			//puts("has wildcard");
			return true;
		}
		i++;
	}
	return false;
}
void argSetter() {
	char ** arguments = Command::_currentSimpleCommand->_arguments;
	//get current number of arguments 
	int i = 0;
	while (arguments[i] != NULL) {
		i++;
	}
	argindex = i;
}
void removeLeftOver() {
	for (int i = 0; i < Command::_currentSimpleCommand->_numOfArguments; i++) {
		char * argument = Command::_currentSimpleCommand->_arguments[i];
		//puts(argument);
		if (hasWildcard(argument)) {
			puts("Leftover");
		}
	}
}
void sortWildcard() {
	//sort after index 0
	//removeLeftOver();
	char ** arguments = Command::_currentSimpleCommand->_arguments;
	int i, j;
	for (i = 2; i < Command::_currentSimpleCommand->_numOfArguments; i++) {
		char* newValue = arguments[i];
		j = i - 1;
		while (j > 0 && strcmp(arguments[j], newValue) > 0) {
			arguments[j + 1] = arguments[j];
			j--;
		}
		arguments[j+1] = newValue;
	}
}
bool doSpecialCase(char* line) {
	int i = 0, count = 0;
	while (line[i] != 0) {
		if (line[i] == '*') {
			//Evaluate count
			//return true iff count == 1
			if (count == 1) {
				return true;
			}
			else {
				return false;
			}
		}
		if (line[i] == '/') {
			count++;
		}
		i++;
	}
	return false;
}

//this works for only strings with *
void expandWildcard(char * prefix, char * suffix) {
	//Base case
	if (suffix[0] == 0) {
		// suffix is empty, put prefix in argument
		//printf("Adding %s\n", prefix);
		if (strlen(prefix) > 2 && prefix[0] == '/' && prefix[1] == '/') {
			//puts("long boi");
			char* fixed = (char*)malloc(sizeof(char) * strlen(prefix));
			int i, j = 0;
			for (i = 0; i < strlen(prefix); i++) {
				fixed[i] = 0;
			}
			for (i = 1; i < strlen(prefix); i++) {
				fixed[j] = prefix[i];
				j++;
			}
			fixed[i] = 0;
			//free(prefix);
			Command::_currentSimpleCommand->insertArgument(strdup(fixed));
		}
		else {
			Command::_currentSimpleCommand->insertArgument(strdup(prefix));
		}
		return;
	}

	// get the next in suffix and then move along suffix
	// check for /, get the word after that
	char * s = NULL;
	if (suffix[0] == '/') {
		s = strchr( (char*)(suffix+1), '/');
	} else {
		s = strchr(suffix, '/');
	}
	char component[100] = ""; // must initialize this
	if ( s != NULL ) { // copy up to the first "/"
		strncpy(component, suffix, s - suffix);
		suffix = s + 1;
	} else { // last part of path, copy the whole thing
		strcpy(component, suffix);
		suffix = suffix + strlen(suffix);
	}

	// expand the wildcard
	char newPrefix[100];
 	if ( strchr(component, '*') == NULL && strchr(component, '?') == NULL ) {
		// no wildcards

		// if prefix is empty
		if ( prefix == NULL || prefix[0] == 0 ) {
			sprintf(newPrefix, "%s", component);
		} else {
			sprintf(newPrefix, "%s/%s", prefix, component);
		}

		expandWildcard(newPrefix, suffix);
		return;
	}

	// has wildcards, translate into a new regex
	char * reg = (char*)malloc(2*strlen(component)+10);	
	char * a = component;
	char * r = reg;

	// copy over all characters, converting to regex representation
	*r = '^';  r++;
	while (*a) {
		if (*a == '*') { // * -> .*
			*r = '.';
			r++;
			*r = '*';
			r++;
		} else if (*a == '?') { // ? -> .*
			*r = '.';   
			r++;
		} else if (*a == '.') { // . -> \\.
			*r = '\\';	
			r++;
			*r = '.';   
			r++;
		} else if (*a == '/') { // remove the slash
			// do nothing
		} else {
			*r = *a; 	
			r++;
		}
		a++;
	}
	/*
	int i = 0;
	int j = 0;
	while(a[i] != NULL) {
		if (a[i] == '*') {
			r[j] = '.';
			j++;
			r[j]
			j++;
		}
		else if (a[i] == '?') {
			r[j] = '.';
			r++;
		}
	}
	*/

	*r = '$';  r++; // end of line
	*r = 0;   // null terminator

	// compile regex
	regex_t re;
	if ( regcomp(&re, reg, REG_EXTENDED|REG_NOSUB) != 0 ) {
		perror("regcomp");
		exit(1);
	}
		
	// if prefix is empty list current directory
	char * dir_name;
	if ( prefix == NULL ) {
		//puts("Prefix is null");
		//Or just remove double slash from string
		const char * dot_char = ".";
		dir_name = strdup(dot_char);
	} else {
		//printf("Prefix is %s\n", prefix);
		dir_name = prefix;
	}
	
	// open the directory
	//printf("Opening: %s\n", dir_name);
	DIR * dir = opendir(dir_name);
	if (dir == NULL) {
		return;
	}

	struct dirent * ent;
	while ( (ent = readdir(dir)) != NULL ) {
		//check if name matches
		if (regexec(&re, ent->d_name, (size_t)0, NULL, 0) == 0) {
			if (prefix == NULL || prefix[0] == 0) {
				sprintf(newPrefix, "%s", ent->d_name);
			} else {
				sprintf(newPrefix, "%s/%s", prefix, ent->d_name);
			}
			if (ent->d_name[0] == '.') { // only add items beginning with . if regex also begins with .
				if (component[0] == '.') {
					expandWildcard(newPrefix, suffix);
				}
			} else {
				expandWildcard(newPrefix, suffix);
			}
		}
	}
}

%}

%%

goal:
  commands
  ;

commands:
  command
  | commands command
  ;

command: simple_command
       ;

simple_command:	
  
  pipe_list iomodifier_list background_opt NEWLINE {
    //printf("   Yacc: Execute command\n");
    Command::_currentCommand.execute();
  }
  | NEWLINE {
	Command::_currentCommand.clear();
	Command::_currentCommand.prompt();
  }
  | error NEWLINE { yyerrok; }
  ;


command_and_args:
  command_word argument_list {
    Command::_currentCommand.insertSimpleCommand( Command::_currentSimpleCommand );
  }
  ;

argument_list:
  argument_list argument
  | /* can be empty */
  ;

argument:
  WORD {
    //printf("   Yacc: insert argument \"%s\"\n", $1);
	//puts("Expanding wildcard");
	//this breaks environment expansion
	if (hasWildcard($1)) {
		//puts("Expanding wildcard");
		//HANDLE Case where prefix is the root directory
		//"/" gives //dev when it should be /dev
		if (doSpecialCase($1)) {
			expandWildcard("/", $1);
		}
		else {
			expandWildcard(NULL, $1);
		}
		sortWildcard();
	}
    Command::_currentSimpleCommand->insertArgument( $1 );
  }
  ;

command_word:
  WORD {
    //printf("   Yacc: insert command \"%s\"\n", $1);
    Command::_currentSimpleCommand = new SimpleCommand();
    Command::_currentSimpleCommand->insertArgument( $1 );
  }
  ;

 /*This bit works for some reason*/
pipe_list:
	pipe_list PIPE {
	} command_and_args {
	}
	| command_and_args {
	}
	;

iomodifier:
  GREAT WORD {
    //printf("   Yacc: insert output \"%s\"\n", $2);
    //char * file = strdup($2);//This solves the double free issues
	if (Command::_currentCommand._outFile) {
		//PLEASE JESUS DON'T CHANGE THIS
		yyerror("Ambiguous output redirect\n");
	}
    Command::_currentCommand._outFile = strdup($2);
  }
  | WEIRDGREAT WORD {
	printf("GOT IT");
  }
  | GREATGREAT WORD {
	//THIS APPENDS SHIT
	//printf("   Yacc: insert output \"%s\"\n", $2);
	
	//char * file = strdup($2);//This solves the double free issues
	//this handles stout to go to file
	if (Command::_currentCommand._outFile) {
		//PLEASE JESUS DON'T CHANGE THIS
		yyerror("Ambiguous output redirect\n");
	}
	Command::_currentCommand._outFile = strdup($2);
	Command::_currentCommand._outAppend = true;
  }
  | GREATGREATAMPERSAND WORD {
	//takes stdout and stderr and puts in a file 
	//and then appends it
	//char * file = strdup($2);//This solves the double free issues
	if (Command::_currentCommand._outFile) {
		//PLEASE JESUS DON'T CHANGE THIS
		yyerror("Ambiguous output redirect\n");
	}
	Command::_currentCommand._outFile = strdup($2);
	Command::_currentCommand._errFile = strdup($2);
  }
  | GREATAMPERSAND WORD {
	//redirect stdout and stderr to a new file
	//DON'T APPEND, just erase and put
	//char * file = strdup($2); //This solves the double free issues
	if (Command::_currentCommand._outFile || Command::_currentCommand._errFile) {
		//PLEASE JESUS DON'T CHANGE THIS
		yyerror("Ambiguous output redirect\n");
	}
	//yyerror("Setting append to true\n");
	//Command::_currentCommand._errAppend = true;
	Command::_currentCommand._outFile = strdup($2);
	Command::_currentCommand._errFile = strdup($2);
  }
  | TWOGREAT WORD {
	if (Command::_currentCommand._errFile) {
		//PLEASE JESUS DON'T CHANGE THIS
		yyerror("Ambiguous output redirect\n");
	}
	Command::_currentCommand._outFile = strdup($2);
	Command::_currentCommand._errFile = strdup($2);
  }
  | LESS WORD {
	//printf("   Yacc: insert output \"%s\"\n", $2);
	//char * file = strdup($2);			//This solves the double free issues
	if (Command::_currentCommand._outFile) {
		//PLEASE JESUS DON'T CHANGE THIS
		yyerror("Ambiguous output redirect\n");
	}
	Command::_currentCommand._outFile = strdup($2);
  }
  ;
iomodifier_list:
	iomodifier_list iomodifier
	| /* empty */
	;
	
background_opt:
	AMPERSAND {
		Command::_currentCommand._background = 1;
	}
	| /* empty */
	;

%%
void
yyerror(const char * s)
{
  fprintf(stderr,"%s", s);
}

#if 0
main()
{
  yyparse();
}
#endif
