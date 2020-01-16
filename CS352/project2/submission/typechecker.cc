#include <stdio.h>
#include <string>
#include <iostream>
using namespace std;
#include "y.tab.hh"
#include "ast.hh"
extern "C" {
        int yylex(void);
        void yyerror(char *);
}
extern FILE *yyin;
//extern std::stack<AST_Node*> parsingStack;
extern Program * program;
extern int yylineno;
extern int yy_flex_debug;
extern int yydebug;
extern bool syntaxErrors;
extern bool cantContinue;

int main(int argc, char ** argv) {
        cout << std::boolalpha;
        yy_flex_debug = 0;
        yydebug = 0;
        if (argc > 1)
                yyin = fopen(argv[1], "r");
        int parseResult = yyparse();
        if (argc > 1) 
                fclose(yyin);
        if (parseResult == 0) {
            //program->printDebug();
            program->check();
            if (!cantContinue)
                program->interpret();
        }  
        return 0;
} 