
/*
 *
 * CS-252 Fall 2017
 * shell.l: lexical analyzer for shell
 * You have to extend it.
 *
 */

%{

//#include <cstring>
#include "y.tab.hh"
#include <string.h>
#include <unistd.h>

static  void yyunput (int c,char *buf_ptr  );

void myunputc(int c) {
  unput(c);
}
extern "C" char * read_line();

int mygetc(FILE * f) {
	static char *p;
	char ch;

	if (!isatty(0)) {
	 // stdin is not a tty. Call real getc
	 return getc(f);
	}

	// stdin is a tty. Call our read_line.

	if (p==NULL || *p == 0) {
	 char * s = read_line();
	 p = s;
	}

	ch = *p;
	p++;

	return ch;
}

#undef getc
#define getc(f) mygetc(f)


%}

%%

\n {
  return NEWLINE;
}

[ \t] {
  /* Discard spaces and tabs */
}

">" {
  return GREAT;
}
">>" {
  return GREATGREAT;
}
"&" {
  return AMPERSAND;
}
">&" {
  return GREATAMPERSAND;
}
">>&" {
  return GREATGREATAMPERSAND;
}
"<" {
  return LESS;
}
"|" {
  return PIPE;
}
"2>" {
  return TWOGREAT;
}

[^ \t\n]*\\[^ \t\n]* {
	//echo lll\< kkkk\\\\\\ uuuu\&
	//FUCK YOU LEX
	//printf("parse this %s\n", yytext);
	char * tok = strdup(yytext);
	int i = 0, slashcount = 0, firstspot = -1, len = 0;
	while(tok[i] != 0) {
		if (tok[i] == '\\') {
			slashcount = slashcount + 1;
			if (firstspot == -1) firstspot = i;
		}
		i = i + 1;
	}
	len = i + 1;
	if (slashcount == 1) {
		//Basic escape like \t
		for (int j = firstspot; j < len; j++) {
			tok[j] = tok[j + 1];
		}
		tok[len - 2] = 0;
		yylval.string_val = tok;
	}
	else {
		int newindex = firstspot;
		bool wasSlash = false;
		for (int j = firstspot; j < len; j++) {
			if (wasSlash) {
				wasSlash = false;

			}
			else if (tok[j] == '\\' && !wasSlash) {
				//printf("skipping %c", tok[j]);
				wasSlash = true;
				continue;
			}
			tok[newindex] = tok[j];
			newindex = newindex + 1;
		}
		yylval.string_val = tok;
	}
	return WORD;
}

`[^\n`]*` {
	//printf("Evaluating subshell");
	//subshell expansion
	//get rid of the stupid ticks
	char * text = strdup(yytext + 1);
	text[strlen(text) - 1] = 0;		//Null terminate
	
	//redirect stdout to a string a
	int tmpin = dup(0);
	int tmpout = dup(1);
	
	int fdpipein[2];
	int fdpipeout[2];
	
	pipe(fdpipein);
	pipe(fdpipeout);
	
	//Create a new command to be ran in the subshell
	write(fdpipein[1], text, strlen(text));
	write(fdpipein[1], "\n", 1);
	write(fdpipein[1], "exit", 4);
	write(fdpipein[1], "\n", 1);
	
	close(fdpipein[1]);
	
	dup2(fdpipein[0], 0);
	close(fdpipein[0]);
	dup2(fdpipeout[1], 1);
	close(fdpipeout[1]);
	
	//Execute
	int ret = fork();
	if (ret == 0) {
		//Call a copy of ourself
		execvp("/proc/self/exe", NULL);
		exit(1);
	}
	else if (ret < 0) {
		perror("fork");
		exit(1);
	}
	
	dup2(tmpin, 0);
	dup2(tmpout, 1);
	close(tmpin);
	close(tmpout);
	
	//Read the output of the subshell
	char c;
	char * buff = (char*) malloc(sizeof(char) * 200);
	int i = 0;
	while (read(fdpipeout[0], &c, 1)) {
		//read result into buffer
		if (c == '\n') {
			buff[i] = ' ';
			//fprintf(stderr, "%c", ' ');
		}
		else {
			buff[i] = c;
			//fprintf(stderr, "%c", c);
		}
		i = i +1;
		//fprintf(stderr, "%c", buff[i]);
	}
	//fprintf(stderr, "that was the result\n");
	close(fdpipein[0]);
	close(fdpipein[1]);
	close(fdpipeout[0]);
	close(fdpipeout[1]);

	//test3  Goodbye!  buffer gets printed when only test3 should be printed
	buff[i - 1] = 0;			//Terminate
	//fprintf(stderr, "buffer: %s\n", buff);
	
	for (i = strlen(buff); i >= 0; i--) {
		//fprintf(stderr, "%c", buff[i]);
		unput(buff[i]);
	}
}


\"[^\n\"]*\" {
	//puts("Quotes");
	//get the word after the first quotation mark first
	//yylval.string_val = strdup(yytext + 1);
	char * newyytext = (char*)(yytext + 1);
	newyytext[strlen(newyytext) - 1] = 0;
	//Support the case where there is no end quotation
	if (yylval.string_val[yyleng-2] == '"') {
		yylval.string_val[yyleng - 2] = 0;		//NULL terminate the last quotation mark away
	}
	yylval.string_val = strdup(newyytext);
	return WORD;
}

[^ ^\\&<>|\t\n$\{\}][^ ^\\&<>|\t\n$\{\}]  {
	//puts("regular word");
  /* Assume that file names have only alpha chars */
  yylval.string_val = strdup(yytext);
  return WORD;
}
[^ ^\\&<>|\t\n][^ ^\\&<>|\t\n]*  {
	//this doesn't work and that's okay
	//printf("Has wildcard!\n");
    yylval.string_val = strdup(yytext);
    return WORD;
}
