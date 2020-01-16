using namespace std;
#include <iostream>
#include <string>
#include <vector>
#ifndef SYMBOLTABLE_H
#define SYMBOLTABLE_H

class AST_Node;
class AST_Type;
class AST_MethodDecl;
class AST_FormalRest;
class AST_ExpList;
class SymbolTable;

// Primitive types
enum PType {
    PINT,
    PBOOL,
    POBJECT,
    PSTRING,
    PVOID,           // For methods
    PUNKNOWN
};
// Symbol types
enum SType {
    SCLASS,
    SVAR,
    SARG,
    SMETHOD,
    SUNKNOWN
};

class ReturnType {
    public:
        bool isArray = false;           //whether an array or not
        int arrayDepth = 0;         //how many dimensions to the array (boolean[] = 1, boolean = 0)
        string objectID;        //If object, the name of the object (ex: objectID = Graph for Graph graph)
        PType type;             //What type this returntype is (e.g. object or boolean or int)
        // Creates a new ReturnType object for an object
        // If not an array, set arrayDepth to 0
        ReturnType(string objectID, int arrayDepth) {
            this->arrayDepth = arrayDepth;
            this->isArray = arrayDepth == 0 ? false : true;
            this->objectID = objectID;
            this->type = POBJECT;
        }
        // Creates a new ReturnType object for a primitive type
        // If not an array, set arrayDepth to 0
        ReturnType(PType type, int arrayDepth) {
            this->arrayDepth = arrayDepth;
            this->isArray = arrayDepth == 0 ? false : true;
            this->type = type;
        }
        ReturnType(PType type){
            this->arrayDepth = 0;
            this->isArray = false;
            this->type = type;
        }
        ReturnType(AST_Type * type);
        ReturnType(AST_FormalRest * formalRest);
        // Creates a new ReturnType object for an unknown type
        ReturnType() {
            this->arrayDepth = 0;
            this->isArray = false;
            this->type = PUNKNOWN;
        }
        bool equal(ReturnType * other);
};

class MethodType {
    public:
        vector<ReturnType*> argTypes;
        ReturnType * returnType;
        int count;              // Number of arguments

        // Checks if argTypes are the same
        bool operator==(const MethodType * other) {
            if (other == NULL)
                return false;
            if (this->argTypes.size() != other->argTypes.size())
                return false;
            for (int i = 0; i < this->argTypes.size(); i++) {
                if (this->argTypes[i] != other->argTypes[i])
                    return false;
            }
            return true;
        }
        void add(PType type, int arrayDepth) {
            argTypes.push_back(new ReturnType(type, arrayDepth));
            count++;
        }
        void add(string id, int arrayDepth) {
            argTypes.push_back(new ReturnType(id, arrayDepth));
            count++;
        }
        void add(ReturnType * returnType) {
            argTypes.push_back(returnType);
            count++;
        }
        MethodType() {
            count = 0;
        }
        string argToString();
};
class ReturnValue {
    //bool false is 0, true is 1
    public:
        ReturnType * returnType;
        union {
            int intValue;
            bool boolValue;
            string * objectValue;
        };
        bool isArray = false;
        bool isObject = false;
        bool isObjectArray = false;

        //object info
        bool initialized;
        SymbolTable * classTable;

        // array info
        int * arr1;
        int ** arr2;
        int arraySize[2];              //Size of each array
        int arrayDepth;               //How many dimensions the array is

        // object array info
        ReturnValue ** objArr1;
        ReturnValue *** objArr2;    // reuses arraySize and arrayDepth
        ReturnValue(int value, int arrayDepth) {
            this->intValue = value;
            returnType = new ReturnType(PINT, arrayDepth);
        }
        ReturnValue(bool value, int arrayDepth) {
            this->boolValue = value;
            returnType = new ReturnType(PBOOL, arrayDepth);
        }
        ReturnValue(string value, int arrayDepth) {
            this->objectValue = new string(value);
            returnType = new ReturnType(value, arrayDepth);
        }
        ReturnValue(int value) {
            this->intValue = value;
            returnType = new ReturnType(PINT, 0);
        }
        ReturnValue(bool value) {
            this->boolValue = value;
            returnType = new ReturnType(PBOOL, 0);
        }
        ReturnValue(string value) {
            this->objectValue = new string(value);
            returnType = new ReturnType(value, 0);
        }
        ReturnValue(ReturnType * returnType) {
            this->returnType = returnType;
            switch (returnType->type) {
                case PINT:
                    this->intValue = 0;
                    break;
                case PBOOL:
                    this->boolValue = false;
                    break;
                case POBJECT:
                    this->objectValue = new string(returnType->objectID);
                    break;
            }
        }
        ReturnValue(const ReturnValue& old) {
            this->returnType = new ReturnType(*old.returnType);
            switch (returnType->type) {
                case PINT:
                    this->intValue = 0;
                    break;
                case PBOOL:
                    this->boolValue = false;
                    break;
                case POBJECT:
                    this->objectValue = new string(returnType->objectID);
                    break;
            }
            isArray = old.isArray;
            isObject = old.isObject;
            isObjectArray = old.isObjectArray;

            //object info
            initialized = old.initialized;
            classTable = old.classTable;

            // array info
            arr1 = old.arr1;
            arr2 = old.arr2;
            arraySize[0] = old.arraySize[0];
            arraySize[1] = old.arraySize[1];
            arrayDepth = old.arrayDepth;
        }
        ReturnValue() {
            this->returnType = new ReturnType();
        }
        void createArray(int size) {createArray(size, 0);}
        void createArray(int size1, int size2);
        void createObjectArray(int size) {createObjectArray(size, 0);}
        void createObjectArray(int size1, int size2);
        void createObject(SymbolTable * classTable);
        void useThisObject(SymbolTable * classTable) {
            isObject = true;
            initialized = true;
            this->classTable = classTable; 
        }
        bool castToBool(int value) {
            if (value <= 0)
                return false;
            else
                return true;
        }
    private:
        void fillArray();
};
class ArgumentTuple {
    public:
        ReturnValue * value;
        string name;
        ArgumentTuple(ReturnValue * value, string name) {
            this->value = value;
            this->name = name;
        }
};
class MethodInvoke {
    public:
        AST_MethodDecl * method;
        vector<ArgumentTuple*> argValues;
        SymbolTable * methodTable;
        SymbolTable * classTable;
        string methodName;
        MethodInvoke(AST_MethodDecl * method, vector<ArgumentTuple*> * args, ReturnValue * object);
        ReturnValue * invoke(bool isMethod, string methodName);
};
class ArgInfo {
    public:
        ReturnValue * returnValue;
        ArgInfo(int value, int arrayDepth) {
            //this->returnType = new ReturnType(PINT, arrayDepth);
            this->returnValue = new ReturnValue(value, arrayDepth);
        }
        ArgInfo(bool value, int arrayDepth) {
            //this->returnType = new ReturnType(PINT, arrayDepth);
            this->returnValue = new ReturnValue(value, arrayDepth);
        }
        ArgInfo(string id, int arrayDepth) {
            //this->returnType = new ReturnType(id, arrayDepth);
            this->returnValue = new ReturnValue(id, arrayDepth);
        }
        ArgInfo(ReturnType * returnType) {
            //this->returnType = returnType;
            this->returnValue = new ReturnValue(returnType);
        }
        ArgInfo(const ArgInfo& old) {
            this->returnValue = new ReturnValue(*(old.returnValue));
        }
        ArgInfo() {
            //this->returnType = new ReturnType();
            this->returnValue = new ReturnValue();
        }
        void printDebug();
};
class MethodInfo {
    public:
        SymbolTable * callTable;    // types filled in at compile time, values filled in during interpretation
        MethodType * methodType;
        MethodInfo(SymbolTable * callTable, MethodType * methodType) {
            this->callTable = callTable;
            this->methodType = methodType;
        }
        MethodInfo(const MethodInfo& old) {
            this->callTable = old.callTable;
            this->methodType = new MethodType(*(old.methodType));
        }
        void printDebug();
};
class VarInfo {
    public:
        ReturnValue * returnValue;
        VarInfo(int value, int arrayDepth) {
            //this->returnType = new ReturnType(PINT, arrayDepth);
            this->returnValue = new ReturnValue(value, arrayDepth);
        }
        VarInfo(bool value, int arrayDepth) {
            //this->returnType = new ReturnType(PBOOL, arrayDepth);
            this->returnValue = new ReturnValue(value, arrayDepth);
        }
        VarInfo(string id, int arrayDepth) {
            //this->returnType = new ReturnType(id, arrayDepth);
            this->returnValue = new ReturnValue(id, arrayDepth);
        }
        VarInfo(ReturnType * returnType) {
            //this->returnType = returnType;
            this->returnValue = new ReturnValue(returnType);
        }
        VarInfo() {
            //this->returnType = new ReturnType();
            this->returnValue = new ReturnValue();
        }
        VarInfo(const VarInfo& old) {
            this->returnValue = new ReturnValue(*(old.returnValue));
        }
        void printDebug();
};
class ClassInfo {
    public:
        bool mainClass;
        ClassInfo(bool mainClass) {this->mainClass = mainClass;}
        ClassInfo(const ClassInfo& old) {
            this->mainClass = old.mainClass;
        }
        void printDebug();
};
class TableRow {
    public:
        string symbol;
        SType symbolType;
        ReturnType * returnType;
        AST_Node * node;
        SymbolTable * table;
        union {
            ArgInfo * argInfo;
            MethodInfo * methodInfo;
            VarInfo * varInfo;
            ClassInfo * classInfo;
        };
        TableRow(string symbol, SType stype, ReturnType * rtype, AST_Node * node, SymbolTable * table) {
            this->symbol = symbol;
            this->symbolType = stype;
            this->returnType = rtype;
            this->node = node;
            this->table = table;
        }
        TableRow(const TableRow& row) {
            this->symbol = row.symbol;
            this->symbolType = row.symbolType;
            this->returnType = row.returnType;
            this->node = row.node;
            this->table = row.table;
            switch (symbolType) {
                case SARG:
                    this->argInfo = new ArgInfo(*(row.argInfo));
                    break;
                case SVAR:
                    this->varInfo = new VarInfo(*(row.varInfo));
                    break;
                case SMETHOD:
                    this->methodInfo = new MethodInfo(*(row.methodInfo));
                    break;
                case SCLASS:
                    this->classInfo = new ClassInfo(*(row.classInfo));
                    break;
            }
        }
        void addArgInfo(ArgInfo * info) {this->argInfo = info;}
        void addMethodInfo(MethodInfo * info) {this->methodInfo = info;}
        void addVarInfo(VarInfo * info) {this->varInfo = info;}
        void addClassInfo(ClassInfo * info) {this->classInfo = info;}
};
class SymbolTable {
    public:
        int symbolCount;
        vector<TableRow *> rows;
        bool addVar(string name, AST_Node * node, ReturnType *  returnType, SymbolTable * table, int arrayDepth);
        bool addMethod(string name, string className, AST_Node * node, MethodType * methodType, SymbolTable * table, SymbolTable * methodTable);
        bool addClass(string name, AST_Node * node, SymbolTable * table, bool mainClass) ;
        bool addArg(string name, AST_Node * node, ReturnType * returnType, SymbolTable * table);
        bool updateSymbolTable(string name, SymbolTable * table);
        bool updateSymbolInfo(string symbol, VarInfo * info);
        bool updateSymbolInfo(string symbol, ArgInfo * info);
        TableRow * getSymbolInfo(string name);
        TableRow * getSymbolInfo(string name, SymbolTable * extendedTable);
        TableRow * getMethodInfo(string name);
        SymbolTable() {symbolCount = 0;}
        // copy constructor
        SymbolTable(const SymbolTable& old, bool newInherited) {
            symbolCount = 0;
            if (newInherited && old.inheritedTable != NULL)
                inheritedTable = new SymbolTable(*(old.inheritedTable), false);
            else
                inheritedTable = old.inheritedTable;
            for (int i = 0; i < old.symbolCount; i++) {
                rows.push_back(new TableRow(*(old.rows[i])));
                symbolCount++;
            }
        }
        SymbolTable * inheritedTable;
        // Returns a symbol name for a method (e.g. Class::method)
        static string methodName(string name, string className) {
            return className + "::" + name;
        }
        void printDebug();
        void inheritTable(SymbolTable * inheritedTable) {this->inheritedTable = inheritedTable;}
    private:
        bool symbolExists(string name);
        bool methodIsName(string symbol, string method);
};
#endif