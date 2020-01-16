using namespace std;
#include <iostream>
#include <string>
#include <vector>
#include <stack>
#include <string.h>
#include "symboltable.hh"

#ifndef AST_H
#define AST_H

// Class name definitions for recursion
// Workaround for recursive class definition/
// https://stackoverflow.com/questions/4300420/recursive-definition-in-cpp
class AST_MainClass;
class AST_ClassDecl;
class AST_VarDecl;
class AST_MethodDecl;
class Exp_BinaryOp;
class Exp_UnaryOp;
class Exp_Index;
class Exp_Length;
class Exp_Parens;
class Exp_IndexLength;
class Exp_ObjectCall;
class AST_Exp;
class Statement_Boolean;
class Statement_Print;
class Statement_Assign;
class Statement_Return;
class AST_Statement;
class Program;
class AST_PrimeType;
class AST_Type;
class AST_FormalRest;
class AST_FormalList;
class AST_ExpRest;
class AST_ExpList;
class AST_Index;
class VarDeclList;
//class Object_NewID;
class Object_NewPrimeType;
class AST_Object;
class StatementList;
class ClassDeclList;
class MethodDeclList;
class FormalRestList;
class ExpRestList;
class SymbolTable;

//Debug function for printing c booleans
const char * pB(int value);

extern int yylineno;
string fixLiteral(string value);
void typeerror(const char * err, int lineno);

//enums
enum Expression {
    Binary,         // Exp op Exp
    Unary,          // ! Exp AND + Exp AND - EXP
    Index,          // id Index
    Length,         // id . length
    Parens,         // ( Exp )
    IndexLength,    // Id Index . length
    INT_LITERAL,
    EBool,           // true AND false
    Object,         
    ObjectCall      // Object . id ( ExpList )
};
enum StoredType {
    Int,
    TBool,
    TID
};
enum StatementType {
    List,       // { Statement* }
    SBool,      // if (Exp) AND while (EXP)
    Print,      // println AND print
    Assign,     // id = Exp AND id Index = Exp
    Return,
    Empty,      // Empty Statement '{ }'
};
enum ObjectType {
    OID,             //id
    This,
    NewID,          //new id ()
    NewPrimeType    //new PrimeType Index
};
enum VarType {
    TypeID,
    IDID
};

// Class Definitions
class AST_MainClass {
    public:
        int lineno;
        string id;
        string argv;
        AST_Statement * statement;
        SymbolTable * symbolTable;
        SymbolTable * globalTable;
        AST_MainClass(char * id, char * argv, AST_Statement * statement) {
            this->id = string(id);
            this->argv = string(argv);
            this->statement = statement;
            saveLine();
        }
        void saveLine() {this->lineno = yylineno;}
        void fillSymbolTable(void (*fn)(const char * err, int lineno), SymbolTable * globalTable);
        void typecheck(void (*fn)(const char * err, int lineno));
};
//class id { VarDecl* MethodDecl* }
class AST_ClassDecl {
    public:
        bool simple;
        string id;
        string extendsId;
        int lineno;
        VarDeclList * varDeclList;
        MethodDeclList * methodDeclList;
        SymbolTable * symbolTable;          // symbol table for the class decl
        SymbolTable * inheritedTable;       // symbol table for the class we extend
        SymbolTable * globalTable;          // symbol table for the whole program
        AST_ClassDecl(char * id, VarDeclList * varDeclList, MethodDeclList * methodDeclList) {
            simple = true;
            this->id = string(id);
            this->varDeclList = varDeclList;
            this->methodDeclList = methodDeclList;
            saveLine();
        }
        AST_ClassDecl(char * id, char * extendsId, VarDeclList * varDeclList, MethodDeclList * methodDeclList) {
            simple = false;
            this->id = string(id);
            this->extendsId = string(extendsId);
            this->varDeclList = varDeclList;
            this->methodDeclList = methodDeclList;
            saveLine();
        }
        void printDebug();
        void saveLine() {this->lineno = yylineno;}
        void fillSymbolTable(void (*fn)(const char * err, int lineno), SymbolTable * globalTable);
        void inheritSymbolTable(void (*fn)(const char * err, int lineno), SymbolTable * inheritedTable);
        void typecheck(void (*fn)(const char * err, int lineno));
};
class AST_VarDecl {
    public:
        VarType varType;
        string idType;              // Name of the type (if object and not an array)
        string name;                // Name of the variable
        int lineno;
        AST_Type * type;            // NULL if vardecl is type (id id -> Graph graph but not Graph[] graph)
        AST_VarDecl(AST_Type * type, char * id) {
            this->type = type;
            this->varType = VarType::TypeID;
            this->name = string(id);
            saveLine();
        }
        AST_VarDecl(char * idType, char * name) {
            this->type = NULL;
            this->idType = string(idType);
            this->name = string(name);
            this->varType = VarType::IDID;
            saveLine();
        }
        void printDebug();
        void saveLine() {this->lineno = yylineno;}

};
class StatementList {
    public:
        vector<AST_Statement*> statements;
        int count;
        StatementList() {
            count = 0;
        }
        StatementList(AST_Statement * statement) {
            StatementList();
            this->add(statement);
        }
        void add(AST_Statement * statement) {
            statements.push_back(statement);
            count++;
        }
        void printDebug();
        ReturnValue * interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke);
};
class AST_MethodDecl {
    public:
        AST_Type * type;
        string id;
        AST_FormalList * list;
        VarDeclList * varDeclList;
        StatementList * statementList;
        AST_Exp *returnExp;
        int lineno;
        SymbolTable * symbolTable;      // symbol table for the method decl
        SymbolTable * classTable;       // symbol table for the encompassing class
        AST_ClassDecl * parentClass;    // Class that contains this method
        AST_MethodDecl(AST_Type * type, char * id, AST_FormalList * list, VarDeclList * varDeclList, StatementList * statementList, AST_Exp *returnExp) {
            this->type = type;
            this->id = string(id);
            this->list = list;
            this->varDeclList = varDeclList;
            if (statementList == NULL)
                this->statementList = new StatementList();
            else
                this->statementList = statementList;
            this->returnExp = returnExp;
            saveLine();
        }
        void printDebug();
        void saveLine() {this->lineno = yylineno;}
        void fillSymbolTable(void (*fn)(const char * err, int lineno), SymbolTable * classTable);
        MethodType * getMethodType();
        void typecheck(void (*fn)(const char * err, int lineno));
};
class Exp_BinaryOp {
    public:
        string op;  //&& || < >  <= >= == != + - * /
        AST_Exp * left;
        AST_Exp * right;
        int lineno;
        Exp_BinaryOp(const char * op, AST_Exp * left, AST_Exp * right) {
            this->op = string(op);
            this->left = left;
            this->right = right;
        }
        ReturnType * typecheck(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl);
        ReturnValue * interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke);
};
class Exp_UnaryOp {
    public:
        char op;    //!, +, -
        AST_Exp * exp;
        int lineno;
        Exp_UnaryOp(char op, AST_Exp * exp) {
            this->op = op;
            this->exp = exp;
        }
        ReturnType * typecheck(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl);
        ReturnValue * interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke);
};
class Exp_Index {
    public:
        string id;
        AST_Index * index;
        int lineno;
        Exp_Index(char * id, AST_Index * index) {
            this->id = string(id);
            this->index = index;
        }
        ReturnType * typecheck(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl);
        ReturnValue * interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke);
};
class Exp_Length {
    public:
        string id;
        int lineno;
        Exp_Length(char * id) {
            this->id = string(id);
        }
        ReturnValue * interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke);
        ReturnType * typecheck(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl);
};
class Exp_Parens {
    public:
        AST_Exp * exp;
        int lineno;
        Exp_Parens(AST_Exp * exp) {
            this->exp = exp;
        }
        ReturnType * typecheck(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl);
        ReturnValue * interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke);
};
class VarDeclList {
    public:
        vector<AST_VarDecl*> varDecls;
        int count;
        VarDeclList() {
            count = 0;
        }
        void add(AST_VarDecl * varDecl) {
            varDecls.push_back(varDecl);
            count++;
        }
        void printDebug();
};
class ClassDeclList {
    public:
        vector<AST_ClassDecl*> classDecls;
        int count;
        ClassDeclList() {
            count = 0;
        }
        void add(AST_ClassDecl * classDecl) {
            classDecls.push_back(classDecl);
            count++;
        }
        void printDebug();
};
class MethodDeclList {
    public:
        vector<AST_MethodDecl*> methodDecls;
        int count;
        MethodDeclList() {
            count = 0;
        }
        void add(AST_MethodDecl * methodDecl) {
            methodDecls.push_back(methodDecl);
            count++;
        }
        void printDebug();
        ReturnValue * interpret();
};
class Exp_IndexLength {
    public:
        string id;
        AST_Index * index;
        int lineno;
        Exp_IndexLength(char * id, AST_Index * index) {
            this->id = string(id);
            this->index = index;
        }
        ReturnType * typecheck(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl);
        ReturnValue * interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke);
};
class Exp_ObjectCall {
    public:
        AST_Object * object;    //object we're calling
        string id;              //method being called
        AST_ExpList * expList;  //argument list that we're calling
        int lineno;
        Exp_ObjectCall(AST_Object * object, char * id, AST_ExpList * expList) {
            this->object = object;
            this->id = string(id);
            this->expList = expList;
        }
        ReturnType * typecheck(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl);
        ReturnValue * interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke);
};
class AST_Exp {
    public:
        Expression expression;
        ReturnType * type;
        bool resolvedType = false;
        int lineno;
        union {
            Exp_BinaryOp * binaryOp;
            Exp_UnaryOp * unaryOp;
            Exp_Index * index;
            Exp_Length * length;
            Exp_Parens * parens;
            Exp_IndexLength * indexLength;
            int intLiteral;
            bool boolLiteral;
            AST_Object * object;
            Exp_ObjectCall * objectCall;
        };
        AST_Exp(const char * op, AST_Exp * leftExp, AST_Exp * rightExp) {
            expression = Expression::Binary;
            binaryOp = new Exp_BinaryOp(op, leftExp, rightExp);
            saveLine();
            binaryOp->lineno = lineno;
        }
        AST_Exp(char op, AST_Exp * exp) {
            expression = Expression::Unary;
            unaryOp = new Exp_UnaryOp(op, exp);
            saveLine();
            unaryOp->lineno = lineno;
        }
        AST_Exp(char * id) {
            expression = Expression::Length;
            length = new Exp_Length(id);
            saveLine();
            length->lineno = lineno;
        }
        AST_Exp(AST_Exp * exp) {
            expression = Expression::Parens;
            parens = new Exp_Parens(exp);
            saveLine();
            parens->lineno = lineno;
        }
        AST_Exp(char * id, AST_Index * index, bool indexLength) {
            saveLine();
            if (indexLength) {
                expression = Expression::IndexLength;
                this->indexLength = new Exp_IndexLength(id, index);
                this->indexLength->lineno = lineno;
            }
            else {
                expression = Expression::Index;
                this->index = new Exp_Index(id, index);
                this->index->lineno = lineno;
            }
        }
        AST_Exp(AST_Object * object, char * id, AST_ExpList * expList) {
            expression = Expression::ObjectCall;
            objectCall = new Exp_ObjectCall(object, id, expList);
            saveLine();
            objectCall->lineno = lineno;
        }
        AST_Exp(int value) {
            expression = Expression::INT_LITERAL;
            intLiteral = value;
            saveLine();
        }
        AST_Exp(bool value) {
            expression = Expression::EBool;
            boolLiteral = value;
            saveLine();
        }
        AST_Exp(AST_Object * object) {
            expression = Expression::Object;
            this->object = object;
            saveLine();
        }
        //PType resolveType(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl);
        ReturnValue * interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke);
        void saveLine() {this->lineno = yylineno;}
        ReturnType * typecheck(void (*fn)(const char * err, int lineno), AST_MainClass * mainClass);
        ReturnType * typecheck(void (*fn)(const char * err, int lineno), AST_MethodDecl * methodDecl);
        ReturnType * typecheck(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl);
};
class Statement_Boolean {
    public:
        // If the boolean statement is an if statement, else it's a while statement
        bool ifStatement;
        AST_Exp * exp;
        AST_Statement * statement;
        AST_Statement * elseStatement;    // Only applies for if statements, NULL if a while statement
        Statement_Boolean(AST_Exp * exp, AST_Statement * whileStatement) {
            this->exp = exp;
            this->statement = whileStatement;
            this->elseStatement = NULL;
            this->ifStatement = false;
        }
        Statement_Boolean(AST_Exp * exp, AST_Statement * trueStatement, AST_Statement * falseStatement) {
            this->exp = exp;
            this->statement = trueStatement;
            this->elseStatement = falseStatement;
            this->ifStatement = true;
        }
        ReturnValue * interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke);
};
class Statement_Print {
    public:
        // Whether the statement is a println() or a print()
        bool println;
        // Whether printing an expression or a string literal
        bool printExp;
        AST_Exp * exp;          // Only if printExp, NULL otherwise
        string stringLiteral;   // Only if !printExp
        Statement_Print(bool println, AST_Exp * exp) {
            this->printExp = true;
            this->println = println;
            this->exp = exp;
        }
        Statement_Print(bool println, char * value) {
            this->printExp = false;
            this->println = println;
            this->stringLiteral = string(value);
            this->stringLiteral = fixLiteral(this->stringLiteral);
            this->exp = NULL;
        }
        ReturnValue * interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke);
};
class Statement_Assign {
    public:
        //if of type 'id Index = Exp', else 'id = Exp'
        bool idIndex;
        string id;
        AST_Index * index;  // Only if ifIndex
        AST_Exp * exp;
        Statement_Assign(char * id, AST_Exp * exp) {
            this->idIndex = false;
            this->id = string(id);
            this->exp = exp;
            this->index = NULL;
        }
        Statement_Assign(char * id, AST_Index * index, AST_Exp * exp) {
            this->idIndex = true;
            this->id = string(id);
            this->exp = exp;
            this->index = index;
        }
        ReturnValue * interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke);
};
class Statement_Return {
    public:
        AST_Exp * exp;
        Statement_Return(AST_Exp * exp) {
            this->exp = exp;
        }
        ReturnValue * interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke);
};
class AST_Statement {
    public:
        StatementType type;
        int lineno;
        union {
            // not sure how to handle list
            StatementList * statementList;
            Statement_Boolean * boolStatement;
            Statement_Print * printStatement;
            Statement_Assign * assignStatement;
            Statement_Return * returnStatement;
        };
        AST_Statement(AST_Exp * exp, AST_Statement * trueStatement, AST_Statement * falseStatement) {
            type = StatementType::SBool;
            boolStatement = new Statement_Boolean(exp, trueStatement, falseStatement);
            saveLine();
        }
        AST_Statement(AST_Exp * exp, AST_Statement * doStatement) {
            type = StatementType::SBool;
            boolStatement = new Statement_Boolean(exp, doStatement);
            saveLine();
        }
        AST_Statement(bool println, AST_Exp * exp) {
            type = StatementType::Print;
            printStatement = new Statement_Print(println, exp);
            saveLine();
        }
        AST_Statement(bool println, char * value) {
            type = StatementType::Print;
            printStatement = new Statement_Print(println, value);
            saveLine();
        }
        AST_Statement(char * id, AST_Exp * exp) {
            type = StatementType::Assign;
            assignStatement = new Statement_Assign(id, exp);
            saveLine();
        }
        AST_Statement(char * id, AST_Index * index, AST_Exp * exp) {
            type = StatementType::Assign;
            assignStatement = new Statement_Assign(id, index, exp);
            saveLine();
        }
        AST_Statement(AST_Exp * exp) {
            type = StatementType::Return;
            returnStatement = new Statement_Return(exp);
            saveLine();
        }
        AST_Statement(StatementList * statementList) {
            type = StatementType::List;
            this->statementList = statementList;
            saveLine();
        }
        AST_Statement() {
            type = StatementType::Empty;
            statementList = NULL;
            saveLine();
        }
        void printDebug();
        ReturnValue * interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke);
        void saveLine() {this->lineno = yylineno;}
        void typecheck(void (*fn)(const char * err, int lineno), AST_MainClass * mainClass);
        void typecheck(void (*fn)(const char * err, int lineno), AST_MethodDecl * methodDecl);
        void typecheck(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl);
};
class Program {
    public:
        AST_MainClass * MainClass;
        ClassDeclList * classDeclList;
        Program(AST_MainClass * mainClass, ClassDeclList * classDeclList) {
            MainClass = mainClass;
            this->classDeclList = classDeclList;
        }
        SymbolTable * symbolTable;
        void interpret();
        void printDebug();
        void check();
        void fillSymbolTable(void (*fn)(const char * err, int lineno));
};
class AST_PrimeType {
    public:
        StoredType type;
        string IDValue; // If an object, the type name is here (if ABCD a; => IDValue = ABCD)
        int lineno;
        AST_PrimeType(int value) {
            type = StoredType::Int;
            saveLine();
        }
        AST_PrimeType(bool value) {
            type = StoredType::TBool;
            saveLine();
        }
        AST_PrimeType(char * value) {
            this->IDValue = string(value);
            type = StoredType::TID;
            saveLine();
        }
        void saveLine() {this->lineno = yylineno;}
};
class AST_Type {
    public:
        bool isArray;
        int lineno;
        int arrayDepth;
        AST_PrimeType * primeType;
        AST_Type(AST_PrimeType * primeType) {
            isArray = false;
            arrayDepth = 0;
            this->primeType = primeType;
            saveLine();
        }
        void increase() {
            isArray = true;
            arrayDepth++;
        }
        void saveLine() {this->lineno = yylineno;}
};
class FormalRestList {
    public:
        vector<AST_FormalRest*> formalRests;
        int count;
        FormalRestList() {
            count = 0;
        }
        void add(AST_FormalRest * formalRest) {
            formalRests.push_back(formalRest);
            count++;
        }
};
class AST_FormalRest {
    public:
        AST_Type * type;
        string id;
        int lineno;
        AST_FormalRest(AST_Type * type, char * id) {
            this->type = type;
            this->id = string(id);
        }
        void saveLine() {this->lineno = yylineno;}
};
class AST_FormalList {
    public:
        bool empty;
        FormalRestList * restList;
        vector<AST_FormalRest*> types;
        int count;
        int lineno;
        AST_FormalList() {
            empty = true;
            count = 0;
            restList = NULL;
            saveLine();
        }
        AST_FormalList(FormalRestList * list) {
            count = 0;
            empty = false;
            this->restList = list;
            this->resolve();
            saveLine();
        }
        void resolve() {
            for (vector<AST_FormalRest*>::iterator formalRest = restList->formalRests.begin(); formalRest != restList->formalRests.end(); formalRest++) {
                types.push_back(*formalRest);
                count++;
            }
        }
        void saveLine() {this->lineno = yylineno;}
};
class ExpRestList {
    public:
        vector<AST_ExpRest*> expRests;
        int count;
        ExpRestList() {
            count = 0;
        }
        void add(AST_ExpRest * expRest) {
            expRests.push_back(expRest);
            count++;
        }
};
class AST_ExpRest {
    public:
        AST_Exp * exp;
        int lineno;
        AST_ExpRest(AST_Exp * exp) {
            this->exp = exp;
            saveLine();
        }
        void saveLine() {this->lineno = yylineno;}
};
class AST_ExpList {
    public:
        AST_Exp * exp;
        ExpRestList * restList;
        vector<AST_Exp*> exps;         // combined list of exp and restList
        int count;
        bool empty;
        int lineno;
        AST_ExpList(AST_Exp * exp, ExpRestList * restList) {
            count = 0;
            empty = false;
            this->exp = exp;
            this->restList = restList;
            this->resolve();
            saveLine();
        }
        AST_ExpList() {
            count = 0;
            empty = true;
            exp = NULL;
            restList = NULL;
            saveLine();
        }
        void resolve() {
            exps.push_back(this->exp);
            count++;
            vector<AST_ExpRest*> expRests = restList->expRests;
            for (vector<AST_ExpRest*>::iterator expRest = expRests.begin(); expRest != expRests.end(); expRest++) {
                exps.push_back((*expRest)->exp);
                count++;
            }
        }
        void saveLine() {this->lineno = yylineno;}
};
class AST_Index {
    public:
        //whether the index is 'Index [Exp]'
        ReturnType * type;
        bool typeSet = false;
        bool recursive;
        int depth;
        AST_Exp * exp;
        AST_Index * index;
        int lineno;
        AST_Index(AST_Exp * exp) {
            this->recursive = false;
            this->exp = exp;
            this->index = NULL;
            saveLine();
        }
        AST_Index(AST_Index * index, AST_Exp * exp) {
            this->recursive = true;
            this->exp = exp;
            this->index = index;
            saveLine();
        }
        void saveLine() {this->lineno = yylineno;}
        void countDepth();
        ReturnType * typecheck(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl);
        ReturnValue * interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke);
};
/*class Object_NewID {
    public:
        string id;
};*/
class Object_NewPrimeType {
    public:
        AST_PrimeType * primeType;
        AST_Index * index;
        Object_NewPrimeType(AST_PrimeType * primeType, AST_Index * index) {
            this->primeType = primeType;
            this->index = index;
        }
};
class AST_Object {
    public:
        ObjectType type;
        int lineno;
        string id;                  // class name, if OID or NewID
        Object_NewPrimeType * newPrimeType;
        AST_Object() {
            type = ObjectType::This;
            saveLine();
        }
        // if newObject then of type 'new id', else of type 'id'
        AST_Object(bool newObject, char * id) {
            if (newObject)
                type = ObjectType::NewID;
            else
                type = ObjectType::OID;
            this->id = string(id);
            saveLine();
        }
        AST_Object(AST_PrimeType * primeType, AST_Index * index) {
            this->newPrimeType = new Object_NewPrimeType(primeType, index);
            this->type = NewPrimeType;
            saveLine();
        }
        void saveLine() {this->lineno = yylineno;}
        ReturnType * typecheck(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl); 
        ReturnValue * interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke);
};
class AST_Node {
    public:
        union {
            class AST_MainClass * astMainClass;
            class SimpleClassDecl * simpleClassDecl;
            class ExtendsClassDecl * extendsClassDecl;
            class AST_ClassDecl * astClassDecl;
            class AST_VarDecl * astVarDecl;
            class VarDeclList * varDeclList;
            class MethodDeclList * methodDeclList;
            class ClassDeclList * classDeclList;
            class FormalRestList * formalRestList;
            class ExpRestList * expRestList;
            class AST_MethodDecl * astMethodDecl;
            class Exp_BinaryOp * expBinaryOp;
            class Exp_UnaryOp * expUnaryOp;
            class Exp_Index * expIndex;
            class Exp_Length * expLength;
            class Exp_Parens * expParens;
            class Exp_IndexLength * expIndexLength;
            class Exp_ObjectCall * expObjectCall;
            class AST_Exp * astExp;
            class StatementList * statementList;
            class Statement_Boolean * statementBoolean;
            class Statement_Print * statementPrint;
            class Statement_Assign * statementAssign;
            class Statement_Return * statementReturn;
            class AST_Statement * astStatement;
            class Program * program;
            class AST_PrimeType * astPrimeType;
            class AST_Type * astType;
            class AST_FormalRest * astFormalRest;
            class AST_FormalList * astFormalList;
            class AST_ExpRest * astExpRest;
            class AST_ExpList * astExpList;
            class AST_Index * astIndex; 
            class AST_Object * astObject;
            class Object_NewPrimeType * objectNewPrimeType;
        };
        AST_Node(AST_Object * astObject) {this->astObject=astObject;}
        AST_Node(AST_MainClass * astMainClass) {this->astMainClass = astMainClass;}
        AST_Node(AST_ClassDecl * astClassDecl) {this->astClassDecl = astClassDecl;}
        AST_Node(AST_VarDecl * astVarDecl) {this->astVarDecl = astVarDecl;}
        AST_Node(AST_MethodDecl * astMethodDecl) {this->astMethodDecl = astMethodDecl;}
        /*AST_Node(Exp_UnaryOp * expUnaryOp) {this->expUnaryOp = expUnaryOp;}
        AST_Node(Exp_Index * expIndex) {this->expIndex = expIndex;}
        AST_Node(Exp_Length * expLength) {this->expLength = expLength;}
        AST_Node(Exp_Parens * expParens) {this->expParens = expParens;}
        AST_Node(Exp_IndexLength * expIndexLength) {this->expIndexLength = expIndexLength;}
        AST_Node(Exp_ObjectCall * expObjectCall) {this->expObjectCall = expObjectCall;}*/
        AST_Node(AST_Exp * astExp) {this->astExp = astExp;}
        AST_Node(Program * program) {this->program = program;}
        AST_Node(AST_PrimeType * astPrimeType) {this->astPrimeType = astPrimeType;}
        AST_Node(AST_Type * astType) {this->astType = astType;}
        AST_Node(AST_FormalRest * astFormalRest) {this->astFormalRest = astFormalRest;}
        AST_Node(AST_FormalList * astFormalList) {this->astFormalList = astFormalList;}
        AST_Node(AST_ExpRest * astExpRest) {this->astExpRest = astExpRest;}
        AST_Node(AST_ExpList * astExpList) {this->astExpList = astExpList;}
        AST_Node(AST_Index * astIndex) {this->astIndex = astIndex;}
        AST_Node(AST_Statement * astStatement) {this->astStatement = astStatement;}
        AST_Node(VarDeclList * varDeclList) {this->varDeclList = varDeclList;}
        AST_Node(ClassDeclList * classDeclList) {this->classDeclList = classDeclList;}
        AST_Node(FormalRestList * formalRestList) {this->formalRestList = formalRestList;}
        AST_Node(MethodDeclList * methodDeclList) {this->methodDeclList = methodDeclList;}
        AST_Node(StatementList * statementList) {this->statementList = statementList;}
        AST_Node(ExpRestList * expRestList) {this->expRestList = expRestList;}
};
#endif
