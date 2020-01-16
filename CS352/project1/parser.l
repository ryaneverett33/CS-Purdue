%{
    #include "y.tab.h"
    #include <stdio.h>
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
"<"                 return LESSTHAN;
">"                 return GREATERTHAN;
"<="                return LESSTHANEQUALTO;
">="                return GREATERTHANEQUALTO;
"=="                return BOOLEQUAL;
"!="                return BOOLNOTEQUAL;
"+"                 return ADD;
"-"                 return SUBTRACT;
"*"                 return MULTIPLY;
"/"                 return DIVIDE;
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
{LETTER}+({LETTER}|{DIGIT}|_)*     return ID;
{DIGIT}+            return INTEGER_LITERAL;
\"(\\.|{NoEscape})*\"           return STRING_LITERAL;
\/\/.*              ;              //This type of comment, IGNORE
"/*"({NoStar}|\*+{NoStarDash})*\*+"/"   ;   /*This type of comment. IGNORE*/
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