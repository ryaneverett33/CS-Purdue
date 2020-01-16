#include <vector>
#include <queue>
#include <map>
#include <iostream>
#include <sstream>
#include "ast.hh"
using namespace std;

class AddressCode;
class Method;
class ILTable;

enum CodeType {
    CSET,               // set an address equal to a value or expression
    CSETNEW,            // set value to new object
    //CSETPOP,            // set value from a pop operation
    CGOBACK,            // return from a branching loop to MARK
    CIF,                // goto a label if expression is true
    CELSE,              // goto a label if previous expression was false
    CSPRINTLN,          // Println a string constant
    CSPRINT,            // Print a string constant
    CPRINTLN,           // Println an expression
    CPRINT,             // Print an expression
    CPUSH,              // Push argument onto stack
    CCALL,              // Call a function that returns a value
    CRETURN,            // Return a value from a function
    CARR,               // sets register to be an array
    CSTORE,             // store value in array
    CGET,               // gets value in array
    CLENGTH,            // gets length of array
    CMARK               // Mark position to return to from branch 
};
enum AddressType {
    Variable,           // x
    SymReg,             // v1 <- v2
    Reg,                // r1
    IntLiteral,         // 1
    BoolLiteral,        // true
    PrintMessage,       // CSPRINTLN message1 (message1 is a global)
    FuncLabel,          // goto label
    PrimType,           // new int, new bool
    Obj,                // Can refer to this or a class
    err
};
enum AddressOp {
    Add,                // 1 + 1
    Sub,                // 1 - 1
    Div,                // 1 / 1
    Mul,                // 1 * 1
    Equal,              // 1 == 1
    GreaterThan,        // 1 > 1
    GreaterThanEqual,   // 1 >= 1
    LessThan,           // 1 < 1
    LessThanEqual,      // 1 <= 1
    And,                // 1 && 1
    Or,                 // 1 || 1
    Not,                // !1
    none
};
enum BinaryCase {
    IntBasic,           // 1 + 1
    IntNest,            // (1+1) + 1 || 1 + (1+1)
    IntTwoNest,         // (1+1)+(1+1)
    IntDoubleNested,    // ((1+1)+(2+2))+((3+3)+(4+4)) OR ((1+1)+(2+2))+(3+3)
    IntExp,             // 1 + x
    ExpBasic,           // x + y
    ExpNest,            // (x+y) + z
    ExpTwoNest,         // (x+y)+(y+z)
    ExpDoubleNested     // ((x+y)+(w+z))+((a+b)+(c+d)) OR ((x+y)+(w+z))+(a+b)
};
struct LastInfo {
    bool isArray = false;
    bool isInit = false;
    bool isClass = false;
    string className;
};

class Global {
    public:
        string name;
        string value;
        Global(string name, string value, bool println) {
            this->name = name; 
            this->value = value;
            if (println)
                this->value = this->value + "\\n";
        }
        Global(string name, string value, int nameOffset, bool println) {
            ostringstream nameStream;
            nameStream << name;
            nameStream << nameOffset;
            this->name = nameStream.str();
            this->value = value;
            if (println)
                this->value = this->value + "\\n";
        }
        // Convert Global to ASM declaration format
        string toInstruction() {
            // println: .asciz \"%d\n\"
            string tmp = string();
            tmp += name;
            tmp += ": .asciz \"";
            tmp += value;
            tmp += "\"";
            return tmp;
        }
};

// Class for compiling/optimzing IL code to ASM
class Compiler {
    public:
        ILTable * table;
        Compiler(ILTable * table) {this->table = table;}
        void compile(Program * program);
        void writeout(string name);
        void compileAddressCode(AddressCode * code, Method * method);
        void compilePrint(AddressCode * code, Method * method);
        void compileIfElse(AddressCode * code, Method * method, bool ifOp);
        void compileCallReturn(AddressCode * code, Method * method, bool isCall);
        void compileMarkGoBack(AddressCode * code, Method * method, bool isMark);
        void compileArray(AddressCode * code, Method * method);
        //void compileLength(AddressCode * code, Method * method);
        void compilePush(AddressCode * code, Method * method);
        void compileSet(AddressCode * code, Method * method);
        void compileSetNew(AddressCode * code, Method * method);
    private:
        void init_constants();
        void compute_offsets();
        void init_alignment();
        void init_method(Method * method);
        void exit_method(Method * method);
        void allocateRegisters(Program * program);
        void basicAllocation(AddressCode * code, bool isMainMethod);
        void addMethod(Method * method);
        void addInstruction(string instruction);
        void addInstruction(const char * str);
        AddressCode * peekNextInstruction();
        AddressCode * consumeNextInstruction();
        TableRow * lookupMethodInfo(SymbolTable * classTable, Method * method);
        TableRow * lookupClassInfo(string className);
        TableRow * lookupClassInfo(Method * method);
        // temporary save of the link register
        void pushLinkRegister();
        // temporary restore of the link register
        void popLinkRegister();
        void saveLinkRegister() {
            addInstruction("MOV r11, lr");
        }
        void restoreLinkRegister() {
            addInstruction("MOV pc, r11");
        }
        void pushStackBase() {
            addInstruction("PUSH {r9}");
        }
        void popStackBase() {
            addInstruction("POP {r9}");
        }
        // call either printf or malloc
        void callStd(bool print) {
            if (print)
                addInstruction("bl printf");
            else
                addInstruction("bl malloc");
        }
        Program * program;
        int curlineno = 0;
        vector<string> * instructions;
        AddressCode * lastInstruction = NULL;
        queue<int> markedLines = queue<int>();            // lines where a MARK occurs
        queue<int> whileLine = queue<int>();              // lines where a branch occurs for a while loop
        struct LastInfo info;
        int currentInstructionCount = -1;
        Method * currentMethod = NULL;
        bool useTab = false;
};
class AddressCode {
    public:
        CodeType type;          // type of code
        AddressOp op;           // operation on code
        AddressType types[3];   // types of each address
        int addressCount;       // number of addresses (up to 3)
        string strAddress[3];   // array of addresses that are strings indexed by types
        int intAddress[3];      // array of addresses that are ints indexed by types
        AddressCode() {
            addressCount = 0;
            types[0] = err;
            types[1] = err;
            types[2] = err;
            intAddress[0] = 0;
            intAddress[1] = 0;
            intAddress[2] = 0;
            strAddress[0] = string();
            strAddress[1] = string();
            strAddress[2] = string();
        }
        // converts address code to string representation
        string str();
        bool isInt(int i);
        string IntToString(int i);
};
class Method {
    public:
        Method() {}
        Method(string name, int * globalCount) {
            this->name = name; 
            this->globalCount = globalCount;
            this->isChild = false;
            this->parent = NULL;
        }
        Method(string name, Method * parent) {
            this->name = name;
            this->parent = parent;
            this->isChild = true;
            this->globalCount = parent->globalCount;
        }
        void addInstruction(AddressCode * instruction) {
            instructions.push_back(instruction);
        }
        string increaseLastInstruction();
        string addGlobal(Global * global) {
            globals.push_back(global);
            *globalCount = *globalCount + 1;
            return global->name;
        }
        void addBranch(Method * branch) {
            branchMethods.push_back(branch);
            branch->parent = this;
        }
        bool isMain() {
            return name.compare("main") == 0;
        }
        // resolves className if branch method
        string getClassName() {
            return getRootParent()->className;
        }
        string getParentName() {
            return getRootParent()->name;
        }
        Method * getRootParent() {
            Method * method = this;
            while (method->isChild) {
                method = method->parent;
            }
            return method;
        }
        static string createMethodName(string className, string methodName);
        static string fixMethodName(string className, string methodName);
        Method * createBranch();
        vector<AddressCode*> instructions;
        vector<Global*> globals;
        vector<Method*> branchMethods;           // branch methods
        int * globalCount;
        bool isChild;                           // is a branch method
        Method * parent;
        string name;                            // name of method (e.g Class_method or Class_method_b0)
        string className;                       // name of the class this method is a part of
        AST_MethodDecl * methodDecl;            // NULL if child
        int targetNumber;                       // if name=Class_method_b5, targetNumber=5
};
//Intermediary Language Table
//Stores methods and globals (string constants)
class ILTable {
    public:
        map<string, Method*> table; //method->instructions
        vector<Global*> globals;
        vector<string> methods;
        int globalCounter = 0;
        Program * program;
        void addMethod(string method, Method * methodObj) {
            table[method] = methodObj;
            methods.push_back(method);
            for (vector<Global*>::iterator global = methodObj->globals.begin(); 
            global != methodObj->globals.end(); global++) {
                addGlobal((*global));
            }
            for (vector<Method*>::iterator branch = methodObj->branchMethods.begin();
            branch != methodObj->branchMethods.end(); branch++) {
                addMethod((*branch)->name, (*branch));
            }
        }
        void addGlobal(Global * global) {
            globals.push_back(global);
        }
};
// Class for converting the AST to IL
class Converter {
    public:
        Converter(){}
        ILTable * convert(Program * program);
        void convertStatement(Method * method, AST_Statement * statement);
        // if storeResult, store result of the expression in 'result'
        string * convertExpression(Method * method, AST_Exp * expression, bool storeResult);
        void convertReturnExpression(Method * method, AST_Exp * exp);
        void debugWriteOut(ILTable * table);
        string * convertBinaryExpression(Method * method, Exp_BinaryOp * expression, bool storeResult);
        string * convertUnaryExpression(Method * method, Exp_UnaryOp * expression, bool storeResult);
        string * convertIndexExpression(Method * method, Exp_Index * expression, bool storeResult);
        string * convertLengthExpression(Method * method, Exp_Length * expression, bool storeResult);
        string * convertIndexLengthExpression(Method * method, Exp_IndexLength * exp, bool storeResult);
        string * convertObjectExpression(Method * method, AST_Object * expression, bool storeResult);
        string * convertObjectCallExpression(Method * method, Exp_ObjectCall * expression, bool storeResult);
    private:
        string * convertExpDoubleNestedCase1(Method * method, Exp_BinaryOp * exp, bool storeResult);
        string * convertExpDoubleNestedCase2(Method * method, Exp_BinaryOp * exp, bool storeResult);
        string * convertExpDoubleNestedCase3(Method * method, Exp_BinaryOp * exp, bool storeResult);
};

// CSET
AddressCode * Set(Method method, string sadd1, int iadd1, AddressType add1,
    string sadd2, int iadd2, AddressType add2, string rawOp);
AddressCode * Set(Method method, string sadd1, int iadd1, AddressType add1,
    string sadd2, int iadd2, AddressType add2,
    string sadd3, int iadd3, AddressType add3, string rawOp);

// CSETNEW
AddressCode * SetNew(Method method, string sadd1, string sadd2, AddressType add1, AddressType add2);

// CSETPOP
//AddressCode * SetPop(Method method, string sadd1, AddressType add1, string sadd2, AddressType add2);

// CGOBACK
AddressCode * GoBack();

// CMARK
AddressCode * Mark();

// CIF, CELSE
AddressCode * BranchIf(string sadd1, int iadd1, AddressType add1,
    string sadd2, int iadd2, AddressType add2, string label, string rawOp);
AddressCode * BranchElse(string label);

// CSPRINTLN, CSPRINT, CPRINT, CPRINTLN
AddressCode * PrintS(string message, bool println);
AddressCode * PrintE(string sadd1, int iadd1, AddressType add1, bool println);

// CPUSH
AddressCode * Push(string sadd1, int iadd1, AddressType add1);

// CCALL
AddressCode * Call(string sadd1, AddressType add1, string sadd2, AddressType add2, 
    string sadd3, AddressType add3);

// CReturn
AddressCode * ReturnV(string sadd1, int iadd1, AddressType add1);

// CARR
AddressCode * Arr(Method method, string sadd1, 
string sadd2, int iadd2, AddressType add2, string sadd3, int iadd3, AddressType add3,
bool is2d);

// CSTORE
AddressCode * Store(Method method, string sadd1, AddressType add1, 
int iadd2, string sadd2, AddressType add2);

// CGET
AddressCode * Get(string sadd1, AddressType add1);

// CLENGTH
AddressCode * LengthV(string sadd1, AddressType add1);

// Auxiliary functions
string OpToStr(AddressOp op);
AddressOp parseOp(string op);
BinaryCase classifyBinary(Exp_BinaryOp * binary, int * subcase);
int parseRegisterTarget(string reg);