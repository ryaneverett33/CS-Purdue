%{
    #include "y.tab.hh"
    extern YYSTYPE yylval;
    #include <stdio.h>
    #include <string.h>
    //removes the quotes
    char * removeQuotes(char * string) {
        char * tmp = strdup(string);
        int len = strlen(string);
        tmp[len - 1] = 0;
        tmp++;
        return tmp;
    }
    //counts instances of newlines and increments yylineno
    void incrementComment(char * text) {
        int len = strlen(text);
        for (int i = 0; i < len; i++) {
            if (text[i] == '\n') {
                yylineno++;
                continue;
            }
            //include support for windows line endings because I'm an idiot
            else if (text[i] == '\r') {
                if (i+1 < len && text[i+1] == '\n') {
                    yylineno++;
                    i++;
                    continue;
                }
            }
        }
    }
%}

DIGIT       [0-9]
LETTER      [a-zA-Z]
NoStar      [^*]
NoStarDash  [^/*]
NoEscape    [^"\\]
%%
[ \t]                   ;
[ \n]|(\r\n)               {yylineno++;}
"System.out.println"            return PRINTLN;
"System.out.print"              return PRINT;
"int"               return INT;
"void"              return VOID;
"if"                return IF;
"else"              return ELSE;
"while"             return WHILE;
"true"              return TTRUE;
"false"             return TFALSE;
"Object"            return OBJECT;
"this"              return THIS;
"new"               return NEW;
"public static void main"       return MAINCLASS;
"class"             return CLASS;
"public"            return PUBLIC;
"String"            return STRING;
"return"            return RETURN;
"length"            return LENGTH;
"boolean"           return BOOLEAN;
"extends"           return EXTENDS;
"++"                return DOUBLEPLUS;
"--"                return DOUBLEMINUS;
"&&"                return BOOLAND;
"||"                return BOOLOR;
"<"                 return '<';
">"                 return '>';
"<="                return LESSTHANEQUALTO;
">="                return GREATERTHANEQUALTO;
"=="                return BOOLEQUAL;
"!="                return BOOLNOTEQUAL;
"+"                 return '+';
"-"                 return '-';
"*"                 return '*';
"/"                 return '/';
"["                 return '[';
"]"                 return ']';
"("                 return '(';
")"                 return ')';
"{"                 return '{';
"}"                 return '}';
"="                 return '=';
"."                 return '.';
";"                 return ';';
"!"                 return '!';
{DIGIT}+                           { yylval.i = atoi(yytext); return INTEGER_LITERAL; }
{LETTER}+({LETTER}|{DIGIT}|_)*     { yylval.s = strdup(yytext); return ID;}
\"(\\.|{NoEscape})*\"              { yylval.s = removeQuotes(yytext); return STRING_LITERAL; }
\/\/.*              ;              //This type of comment, IGNORE
"/*"({NoStar}|\*+{NoStarDash})*\*+"/"   {incrementComment(yytext);}
.                   return yytext[0];
%%
/*void yyerror(const char *str) {
        fprintf(stderr,"error: %s\n",str);
}
 
int yywrap() {
        return 1;
} 
  
int main() {
    while (1) {
        int tok = yylex();
        printf("Token: %d\n", tok);
    }
} */