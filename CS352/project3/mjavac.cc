#include <stdio.h>
#include <string>
#include <iostream>
using namespace std;
#include "y.tab.hh"
#include "ast.hh"
#include "compile.hh"
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
            program->resolveProgramName(argv[1]);
            program->check();
            if (!cantContinue) {
                program->optimize();
                //program->interpret();
                Converter * converter = new Converter();
                ILTable * table = converter->convert(program);
                converter->debugWriteOut(table);
                Compiler * compiler = new Compiler(table);
                compiler->compile(program);
            }
        }  
        return 0;
} 