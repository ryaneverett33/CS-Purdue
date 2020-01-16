%{
        #include <stdio.h>
        #include <stack>
        #include "ast.hh"
        #ifdef lib
        extern "C" {
                void yyerror(const char *);  
        }
        #else
        void yyerror(const char *);
        #endif
        int yylex(void);
        extern FILE *yyin;
        extern int yylineno;
        extern int yy_flex_debug;
        extern int yydebug;
        extern char * yytext;
        //old parsing stack
        //std::stack<AST_Node*> parsingStack;
        Program * program = NULL;
%}

%token PRINTLN INT VOID IF WHILE TTRUE TFALSE OBJECT THIS NEW MAINCLASS
%token CLASS PUBLIC STRING RETURN LENGTH DOUBLEPLUS BOOLAND BOOLOR
%token LESSTHANEQUALTO GREATERTHANEQUALTO
%token BOOLEQUAL BOOLNOTEQUAL ID
%token INTEGER_LITERAL STRING_LITERAL BOOLEAN EXTENDS ELSE
%token INVALID DOUBLEMINUS PRINT

%union {
        char * s;
        bool b;
        int i;
        char c;
        class AST_Node * n;
        int tok;
}
%type <s> ID STRING_LITERAL
%type <b> TTRUE TFALSE
%type <i> INTEGER_LITERAL
%type <n> Program MainClass ClassDeclList ClassDecl MethodDeclList MethodDecl FormalList FormalRestList ObjectB TypeB
%type <n> Type PrimeType VarDeclList VarDecl Object StatementList Statement Index ExpList ExpRestList ExpRest Exp PrimeTypeB
%type <n> FormalRest
%type <tok> NEW

%left BOOLEQUAL BOOLNOTEQUAL
%left BOOLAND BOOLOR
%left LESSTHANEQUALTO GREATERTHANEQUALTO
%left '<' '>'
%left '!'
%left '*' '/'
%left '+' '-'

%%
Program: MainClass[mc] ClassDeclList[cdl] {program = new Program($mc->astMainClass, $cdl->classDeclList);}
        ;
MainClass: CLASS ID[id1] '{' MAINCLASS '(' STRING '[' ']' ID[id2] ')' '{' Statement[s] '}' '}' 
        {$$ = new AST_Node(new AST_MainClass($id1, $id2, $s->astStatement));}
        ;
ClassDeclList: ClassDeclList[list] ClassDecl[decl] {$list->classDeclList->add($decl->astClassDecl);}
        | /* empty rule */ {$$ = new AST_Node(new ClassDeclList());}
        ;
ClassDecl: CLASS ID[id] '{' VarDeclList[vdl] MethodDeclList[mdl] '}' {$$ = new AST_Node(new AST_ClassDecl($id, $vdl->varDeclList, $mdl->methodDeclList));}
        | CLASS ID[id1] EXTENDS ID[id2] '{' VarDeclList[vdl] MethodDeclList[mdl] '}' {$$ = new AST_Node(new AST_ClassDecl($id1, $id2, $vdl->varDeclList, $mdl->methodDeclList));}
        ;
MethodDeclList: MethodDeclList[list] MethodDecl[decl] {$list->methodDeclList->add($decl->astMethodDecl);}
        | {$$ = new AST_Node(new MethodDeclList());}
        ;
MethodDecl: PUBLIC Type[t] ID[id] '(' FormalList[fl] ')' '{' VarDeclList[vdl] StatementList[sl] RETURN Exp[e] ';' '}'
        {$$ = new AST_Node(new AST_MethodDecl($t->astType, $id, $fl->astFormalList, $vdl->varDeclList, $sl->statementList, $e->astExp));}
        | PUBLIC Type[t] ID[id] '(' FormalList[fl] ')' '{' VarDeclList[vdl] RETURN Exp[e] ';' '}'
        {$$ = new AST_Node(new AST_MethodDecl($t->astType, $id, $fl->astFormalList, $vdl->varDeclList, NULL, $e->astExp));}
        ;
FormalList: Type[t] ID[id] FormalRestList[list] {
    $list->formalRestList->add(new AST_FormalRest($t->astType, $id)); $$ = new AST_Node(new AST_FormalList($list->formalRestList));}
        | {$$ = new AST_Node(new AST_FormalList());}
        ;
FormalRestList: FormalRestList[list] FormalRest[var] {$list->formalRestList->add($var->astFormalRest);}
        | {$$ = new AST_Node(new FormalRestList());}
        ;
FormalRest: ',' Type[t] ID[id] {$$ = new AST_Node(new AST_FormalRest($t->astType, $id));}
        ;
Type: PrimeType[pt] {$$ = new AST_Node(new AST_Type($pt->astPrimeType));}
        | Type[t] '[' ']' {$t->astType->increase();}
        ;
PrimeType: INT {$$ = new AST_Node(new AST_PrimeType(1));}
        | BOOLEAN {$$ = new AST_Node(new AST_PrimeType(true));}
        | ID[i] {$$ = new AST_Node(new AST_PrimeType($i));}
        ;
TypeB: PrimeTypeB[pt]  {$$ = new AST_Node(new AST_Type($pt->astPrimeType));}
        | TypeB[t] '[' ']' {$t->astType->increase();}
        | ID[id] '[' ']' {
            AST_Type * type = new AST_Type(new AST_PrimeType($id)); type->increase(); $$ = new AST_Node(type);
            }
        ;
PrimeTypeB: INT {$$ = new AST_Node(new AST_PrimeType(1));}
        | BOOLEAN {$$ = new AST_Node(new AST_PrimeType(true));}
        ;
VarDeclList: VarDeclList[vdl] VarDecl[var] {$vdl->varDeclList->add($var->astVarDecl);}
        | {$$ = new AST_Node(new VarDeclList());}
        ;
VarDecl: TypeB[t] ID[id] ';' { $$ = new AST_Node(new AST_VarDecl($t->astType, $id));}
        | ID[id1] ID[id2] ';' { $$ = new AST_Node(new AST_VarDecl($id1, $id2));}
        ;
Object: ID {$$ = new AST_Node(new AST_Object(false, $1));}
        | THIS  {$$ = new AST_Node(new AST_Object());}
        | NEW ID[id] '(' ')' { $$ = new AST_Node(new AST_Object(true, $2));}
        | NEW PrimeType[p] Index[i] { $$ = new AST_Node(new AST_Object($p->astPrimeType, $i->astIndex));}
        ;
ObjectB: THIS {$$ = new AST_Node(new AST_Object());}
        | NEW ID[id] '(' ')' {
            char * id = $id;
            int lineno = yylineno;
            $$ = new AST_Node(new AST_Object(true, $id));
            }
        | NEW PrimeType[pt] Index[in] {$$ = new AST_Node(new AST_Object($pt->astPrimeType, $in->astIndex));}
        ;
StatementList: StatementList[list] Statement[s] {$list->statementList->add($s->astStatement);}
        | Statement[s] {$$ = new AST_Node(new StatementList($s->astStatement));}
        ;
Statement: '{' StatementList[list] '}' {$$ = new AST_Node(new AST_Statement($list->statementList));}
        | '{' '}' {$$ = new AST_Node(new AST_Statement());}
        | IF '(' Exp[e] ')' Statement[s1] ELSE Statement[s2] {$$ = new AST_Node(new AST_Statement($e->astExp, $s1->astStatement, $s2->astStatement));}
        | WHILE '(' Exp[e] ')' Statement[s] {$$ = new AST_Node(new AST_Statement($e->astExp, $s->astStatement));}
        | PRINTLN '(' Exp[e] ')' ';' {$$ = new AST_Node(new AST_Statement(true, $e->astExp));}
        | PRINTLN '(' STRING_LITERAL[s] ')' ';' {$$ = new AST_Node(new AST_Statement(true, $s));}
        | PRINT '(' Exp[e] ')' ';' {$$ = new AST_Node(new AST_Statement(false, $e->astExp));}
        | PRINT '(' STRING_LITERAL[s] ')' ';' {$$ = new AST_Node(new AST_Statement(false, $s));}
        | ID[i] '=' Exp[e] ';' {$$ = new AST_Node(new AST_Statement($i, $e->astExp));}
        | ID[id] Index[in] '=' Exp[e] ';' {$$ = new AST_Node(new AST_Statement($id, $in->astIndex, $e->astExp));}
        | RETURN Exp[e] ';' {$$ = new AST_Node(new AST_Statement($e->astExp));}
        ;
Index: '[' Exp[e] ']' {$$ = new AST_Node(new AST_Index($e->astExp));}
        | Index[in] '[' Exp[e] ']' {$$ = new AST_Node(new AST_Index($in->astIndex, $e->astExp));}
        ;
Exp: Exp[e1] BOOLAND Exp[e2] {$$ = new AST_Node(new AST_Exp("&&", $e1->astExp, $e2->astExp));}
        | Exp[e1] BOOLOR Exp[e2] {$$ = new AST_Node(new AST_Exp("||", $e1->astExp, $e2->astExp));}
        | Exp[e1] BOOLEQUAL Exp[e2] {$$ = new AST_Node(new AST_Exp("==", $e1->astExp, $e2->astExp));}
        | Exp[e1] BOOLNOTEQUAL Exp[e2] {$$ = new AST_Node(new AST_Exp("!=", $e1->astExp, $e2->astExp));}
        | Exp[e1] LESSTHANEQUALTO Exp[e2] {$$ = new AST_Node(new AST_Exp("<=", $e1->astExp, $e2->astExp));}
        | Exp[e1] GREATERTHANEQUALTO Exp[e2] {$$ = new AST_Node(new AST_Exp(">=", $e1->astExp, $e2->astExp));}
        | Exp[e1] '<' Exp[e2] {$$ = new AST_Node(new AST_Exp("<", $e1->astExp, $e2->astExp));}
        | Exp[e1] '>' Exp[e2] {$$ = new AST_Node(new AST_Exp(">", $e1->astExp, $e2->astExp));}
        | Exp[e1] '+' Exp[e2] {$$ = new AST_Node(new AST_Exp("+", $e1->astExp, $e2->astExp));}
        | Exp[e1] '-' Exp[e2] {$$ = new AST_Node(new AST_Exp("-", $e1->astExp, $e2->astExp));}
        | Exp[e1] '*' Exp[e2] {$$ = new AST_Node(new AST_Exp("*", $e1->astExp, $e2->astExp));}
        | Exp[e1] '/' Exp[e2] {$$ = new AST_Node(new AST_Exp("/", $e1->astExp, $e2->astExp));}
        | '!' Exp[e] {$$ = new AST_Node(new AST_Exp('!', $e->astExp));}
        | '-' Exp[e] {$$ = new AST_Node(new AST_Exp('-', $e->astExp));}
        | '+' Exp[e] {$$ = new AST_Node(new AST_Exp('+', $e->astExp));}
        | INTEGER_LITERAL[i] {$$ = new AST_Node(new AST_Exp($i));}
        | TTRUE {$$ = new AST_Node(new AST_Exp(true));}
        | TFALSE {$$ = new AST_Node(new AST_Exp(false));}
        | Object[o] {$$ = new AST_Node(new AST_Exp($o->astObject));}
        | '(' Exp[e] ')' {$$ = new AST_Node(new AST_Exp($e->astExp));}
        | ID[id] Index[in] {$$ = new AST_Node(new AST_Exp($id, $in->astIndex, false));}
        | ID[id] '.' LENGTH {$$ = new AST_Node(new AST_Exp($id));}
        | ID[id] Index[in] '.' LENGTH {$$ = new AST_Node(new AST_Exp($id, $in->astIndex, true));}
        // Equivalent to Object.id()
        | ID[id1] '.' ID[id2] '(' ExpList[el] ')' {
            AST_Object * obj = new AST_Object(false, $id1); $$ = new AST_Node(new AST_Exp(obj, $id2, $el->astExpList));}
        | ObjectB[op] '.' ID[id] '(' ExpList[el] ')' {$$ = new AST_Node(new AST_Exp($op->astObject, $id, $el->astExpList));}
        ;
ExpList: Exp[e] ExpRestList[list] {$$ = new AST_Node(new AST_ExpList($e->astExp, $list->expRestList));}
        | {$$ = new AST_Node(new AST_ExpList());}
        ;
ExpRestList: ExpRestList[list] ExpRest[e] {$list->expRestList->add($e->astExpRest);}
        | {$$ = new AST_Node(new ExpRestList());}
        ;
ExpRest: ',' Exp[e] {$$ = new AST_Node(new AST_ExpRest($e->astExp));}
        ;
%%
#ifdef lib
extern "C" {
        void yyerror(const char *str) {
                fprintf(stderr,"Syntax errors in line %d\n", yylineno);
        }
        
        int yywrap() {
                return 1;
        } 
}
#else
void yyerror(const char *str) {
    fprintf(stderr,"Syntax errors in line %d\n", yylineno);
}
 
int yywrap() {
        return 1;
} 
#endif

#ifndef lib
int main(int argc, char ** argv) {
        yy_flex_debug = 0;
        if (argc > 1)
                yyin = fopen(argv[1], "r");
        yyparse();
        if (argc > 1) 
                fclose(yyin);
        return 0;
} 
#endif