%{
        #include <stdio.h>
        int yylex(void);
        void yyerror(char *);
        extern FILE *yyin;
        extern int yylineno;
        extern int yy_flex_debug;
%}

%token PRINTLN INT VOID IF WHILE TTRUE TFALSE OBJECT THIS NEW MAINCLASS
%token CLASS PUBLIC STRING RETURN LENGTH DOUBLEPLUS BOOLAND BOOLOR
%token LESSTHAN GREATERTHAN LESSTHANEQUALTO GREATERTHANEQUALTO
%token BOOLEQUAL BOOLNOTEQUAL ADD SUBTRACT MULTIPLY DIVIDE ID
%token INTEGER_LITERAL STRING_LITERAL BOOLEAN EXTENDS ELSE
%token INVALID DOUBLEMINUS
%%
Program: MainClass ClassDeclList
        ;
MainClass: CLASS ID '{' MAINCLASS '(' STRING '['']' ID ')'
        '{' Statement '}' '}'
        ;
ClassDeclList: ClassDeclList ClassDecl
        | /* empty rule */
        ;
ClassDecl: CLASS ID '{' VarDeclList MethodDeclList '}'
        | CLASS ID EXTENDS ID '{' VarDeclList MethodDeclList '}'
        ;
MethodDeclList: MethodDeclList MethodDecl
        | /* empty rule */
        ;
MethodDecl: PUBLIC Type ID '(' FormalList ')'
        '{' VarDeclList StatementList RETURN Exp ';' '}'
        ;
FormalList: Type ID FormalRestList
        | /* empty rule */
        ;
FormalRestList: FormalRestList FormalRest
        | /* empty rule */
        ;
FormalRest: ',' Type ID
        ;
Type: ID
        | INT
        | BOOLEAN
        | Type '['']'
        ;
VarDeclList: VarDeclList VarDecl
        | /* empty rule */
        ;
VarDecl: Type ID ';'
        | ID '=' Exp ';'
        ;
Object: ID
        | THIS
        | NEW ID '(' ')'
        | NEW Type Index
        ;
StatementList: StatementList Statement
        | /* empty rule */
        ;
Statement: '{' StatementList '}'
        | IF '(' Exp ')' Statement ELSE Statement
        | WHILE '(' Exp ')' Statement
        | PRINTLN '(' Exp ')' ';'
        | PRINTLN '(' STRING_LITERAL ')' ';'
        | ID '=' Exp ';'
        | ID Index '=' Exp ';'
        ;
Index: '[' Exp ']'
        | Index '[' Exp ']'
        ;
Exp: Exp BOOLOR Exp1
        | Exp1
        ;
Exp1: Exp1 BOOLAND Exp2
        | Exp2
        ;
Exp2: Exp2 BOOLEQUAL Exp3
        | Exp2 BOOLNOTEQUAL Exp3
        | Exp3
        ;
Exp3: Exp3 LESSTHAN Exp4
        | Exp3 LESSTHANEQUALTO Exp4
        | Exp3 GREATERTHAN Exp4
        | Exp3 GREATERTHANEQUALTO Exp4
        | Exp4
        ;
Exp4: Exp4 ADD Exp5
        | Exp4 SUBTRACT Exp5
        | Exp5
        ;
Exp5: Exp5 MULTIPLY Exp6
        | Exp5 DIVIDE Exp6
        | Exp6
        ;
// ! Exp, + Exp, - Exp
Exp6: '!' Exp7
        | ADD Exp7
        | SUBTRACT Exp7
        | Exp7
        ;
Exp7: Exp7 '.' LENGTH
        | Exp7 '.' ID '(' ExpList ')'
        | Exp8
        ;
Exp8: ID BaseExp '.' LENGTH
        | BaseExp
        ;
BaseExp: '(' Exp ')'
        | ID Index
        | INTEGER_LITERAL
        | TTRUE
        | TFALSE
        | Object
        ;
ExpList: Exp ExpRestList
        | /* empty rule */
        ;
ExpRestList: ExpRestList ExpRest
        | /* empty rule */
        ;
ExpRest: ',' Exp
        ;
%%
void yyerror(char *str) {
        fprintf(stderr,"Syntax errors in line %d\n", yylineno);
}
 
int yywrap() {
        return 1;
} 
  
int main(int argc, char ** argv) {
        yy_flex_debug = 0;
        if (argc > 1)
                yyin = fopen(argv[1], "r");
        yyparse();
        if (argc > 1) 
                fclose(yyin);
        return 0;
} 