#include "symboltable.hh"
#include "ast.hh"

PType fromStoredType(StoredType type);
void addVarDecl(void (*fn)(const char * err, int lineno), AST_VarDecl* varDecl, SymbolTable * symbolTable, int lineno);
void addArg(void (*fn)(const char * err, int lineno), AST_FormalRest* formalRest, SymbolTable * symbolTable, int lineno);
void addMethod(void (*fn)(const char * err, int lineno), string className, AST_MethodDecl* methodDecl, SymbolTable * symbolTable, int lineno);
bool cantContinue = false;

//enum cout print
std::ostream& operator<<(std::ostream& out, const Expression value){
    switch(value) {
        case Binary:
            return out << "Binary";
        case Unary:
            return out << "Unary";
        case Index:
            return out << "Index";
        case Length:
            return out << "Length";
        case Parens:
            return out << "Parens";
        case IndexLength:
            return out << "IndexLength";
        case INT_LITERAL:
            return out << "INTEGER_LITERAL";
        case EBool:
            return out << "Boolean";
        case Object:
            return out << "Object";
        case ObjectCall:
            return out << "ObjectCall";
        default:
            return out << "UNKNOWN";
    }
}
std::ostream& operator<<(std::ostream& out, const StoredType value){
    switch(value) {
        case Int:
            return cout << "Int";
        case TBool:
            return cout << "Boolean";
        case TID:
            return cout << "ID";
        default:
            return cout << "UNKNOWN";
    }
}
std::ostream& operator<<(std::ostream& out, const StatementType value){
    switch(value) {
        case List:
            return cout << "List";
        case SBool:
            return cout << "Boolean";
        case Print:
            return cout << "Print";
        case Assign:
            return cout << "Assign";
        case Return:
            return cout << "Return";
        case Empty:
            return cout << "Empty";
        default:
            return cout << "UNKNOWN";
    }
}
std::ostream& operator<<(std::ostream& out, const ObjectType value){
    switch(value) {
        case OID:
            return cout << "ID";
        case This:
            return cout << "This";
        case NewID:
            return cout << "NewID";
        case NewPrimeType:
            return cout << "NewPrimeType";
        default:
            return cout << "UNKNOWN";
    }
}
std::ostream& operator<<(std::ostream& out, const VarType value){
    switch(value) {
        case TypeID:
            return cout << "Type ID";
        case IDID:
            return cout << "ID ID";
        default:
            return cout << "UNKNOWN";
    }
}

void Program::interpret() {
    MainClass->statement->interpret(false, MainClass, NULL);
}
void Program::printDebug() {
    // print # of classes
    cout << "Main Class:" << endl;
    cout << "id: " << MainClass->id << endl << "argv: " << MainClass->argv << endl;
    MainClass->statement->printDebug();
    cout << "Program has " << classDeclList->count << " additional classes" << endl;
    classDeclList->printDebug();
}
// typecheck
void Program::check() {
    // create global symbol table
    // create symbol table for each class, back to front
    //      create symbol table for each method in each class
    // Report any symbols that already exist
    // resolve any issues

    // create global symbol table
    this->symbolTable = new SymbolTable();
    this->fillSymbolTable(&typeerror);
    
    // create symbol table for each class and for each method in the class
    for (vector<AST_ClassDecl*>::iterator classDecl = classDeclList->classDecls.begin(); classDecl != classDeclList->classDecls.end(); classDecl++) {
        (*classDecl)->fillSymbolTable(&typeerror, this->symbolTable);
        
        // Update global symbol table to point to individual tables
        if (symbolTable->updateSymbolTable((*classDecl)->id, (*classDecl)->symbolTable)) {
            //cout << "Update global table for " << (*classDecl)->id << endl;
        }
    }
    //this->symbolTable->printDebug();
    //MainClass->fillSymbolTable(&typeerror, this->symbolTable);
    // resolve inherited symbol tables
    for (vector<AST_ClassDecl*>::iterator classDecl = classDeclList->classDecls.begin(); classDecl != classDeclList->classDecls.end(); classDecl++) {
        if (!(*classDecl)->simple) {
            // extends another class, so inherits the other symbol table
            TableRow * row = symbolTable->getSymbolInfo((*classDecl)->extendsId);
            if (row == NULL) {
                //cout << "Class " << (*classDecl)->id << " extends a class " << (*classDecl)->extendsId << " that doesn't exist" << endl;
                //exit(-1);
                cantContinue = true;
                cout << "Type Violation in Line " << (*classDecl)->lineno << endl;
                continue;
            }
            //(*classDecl)->inheritSymbolTable(&typeerror, row->table);
            (*classDecl)->inheritedTable = row->table;
            (*classDecl)->symbolTable->inheritTable(row->table);
        }
    }

    // check statements and expressions for valid symbols and correct type usage

    // check main class
    //cout << "typechecking " << MainClass->id << endl;
    MainClass->typecheck(&typeerror);

    // check all other classes
    for (vector<AST_ClassDecl*>::iterator classDecl = classDeclList->classDecls.begin(); classDecl != classDeclList->classDecls.end(); classDecl++) {
        //cout << "typechecking " << (*classDecl)->id << endl;
        (*classDecl)->typecheck(&typeerror);
    }
}
void Program::fillSymbolTable(void (*fn)(const char * err, int lineno)) {
    for (vector<AST_ClassDecl*>::iterator classDecl = classDeclList->classDecls.begin();
    classDecl != classDeclList->classDecls.end(); classDecl++) {
        this->symbolTable->addClass((*classDecl)->id, new AST_Node((*classDecl)), symbolTable, false);
    }
    this->symbolTable->addClass(MainClass->id, new AST_Node(MainClass), symbolTable, true);
    MainClass->globalTable = symbolTable;
    MainClass->symbolTable = new SymbolTable();         // Don't fill it because main class can't have any arguments
}
void AST_ClassDecl::fillSymbolTable(void (*fn)(const char * err, int lineno), SymbolTable * globalTable) {
    this->symbolTable = new SymbolTable(); 
    this->globalTable = globalTable;
    for (vector<AST_VarDecl*>::iterator varDecl = varDeclList->varDecls.begin(); varDecl != varDeclList->varDecls.end(); varDecl++) {
        // Add all symbols to table
        addVarDecl(fn, (*varDecl), symbolTable, lineno);
    }
    for (vector<AST_MethodDecl*>::iterator methDecl = methodDeclList->methodDecls.begin(); methDecl != methodDeclList->methodDecls.end(); methDecl++) {
        // add methods to this->symbolTable
        addMethod(fn, this->id, (*methDecl), this->symbolTable, lineno);

        // create method's symbol table
        (*methDecl)->fillSymbolTable(fn, this->symbolTable);

        // class row for method should point to method's table
        symbolTable->updateSymbolTable(SymbolTable::methodName((*methDecl)->id, id), (*methDecl)->symbolTable);

        // give method reference to this class
        (*methDecl)->parentClass = this;
    }
}
void AST_ClassDecl::typecheck(void (*fn)(const char * err, int lineno)) {
    for (vector<AST_MethodDecl*>::iterator methDecl = methodDeclList->methodDecls.begin(); methDecl != methodDeclList->methodDecls.end(); methDecl++) {
        //cout << "typechecking " << (*methDecl)->id << endl;
        (*methDecl)->typecheck(fn);
    }
}
// add methods and variables found in the superclass's table that do not exist in the extended class's table
// If a extends b -> a inherits b's table
/*void AST_ClassDecl::inheritSymbolTable(void (*fn)(const char * err, int lineno), SymbolTable * inheritedTable) {

}
void AST_MainClass::fillSymbolTable(void (*fn)(const char * err, int lineno), SymbolTable * globalTable) {
}*/
void AST_MainClass::typecheck(void (*fn)(const char * err, int lineno)) {
    statement->typecheck(fn, this);
}
void AST_MethodDecl::fillSymbolTable(void (*fn)(const char * err, int lineno), SymbolTable * classTable) {
    this->symbolTable = new SymbolTable();
    this->classTable = classTable;
    // Add variable declarations
    for (vector<AST_VarDecl*>::iterator varDecl = varDeclList->varDecls.begin(); varDecl != varDeclList->varDecls.end(); varDecl++) {
        // Add all symbols to table
        addVarDecl(fn, (*varDecl), symbolTable, lineno);
    }
    // Add arguments
    if (!list->empty) {
        for (vector<AST_FormalRest*>::iterator formalRest = list->types.begin(); formalRest != list->types.end(); formalRest++) {
            // Add all symbols to table
            addArg(fn, (*formalRest), symbolTable, lineno);
        }
    }
    //cout << "Symbol Table debug for method " << this->id << endl;
    //this->symbolTable->printDebug();
}
void AST_MethodDecl::typecheck(void (*fn)(const char * err, int lineno)) {
    for (vector<AST_Statement*>::iterator statement = statementList->statements.begin();
    statement != statementList->statements.end(); statement++) {
        (*statement)->typecheck(fn, this);
    }
    // typecheck the return exp
    //returnExp->typecheck(fn, this);
    // check exp type is the same as methoddecl 
    //PType type = returnExp->resolveType(fn, false, NULL, this);
    ReturnType * type = returnExp->typecheck(fn, this);
    if (type == NULL)
        return;
    MethodType * methodType = getMethodType();
    if (!type->equal(methodType->returnType)) {
        fn("Return type does not match method type", lineno);
    }
}
MethodType * AST_MethodDecl::getMethodType() {
    MethodType * type = new MethodType();
    if (!list->empty) {
        /*for (vector<AST_FormalRest*>::iterator formalRest = list->types.end(); formalRest != list->types.begin(); formalRest--) {
            // Add all symbols to table
            //type->add(fromStoredType((*formalRest)->type->primeType->type));
            type->add(new ReturnType((*formalRest)->type));
        }*/
        // add methods in backwards
        for (int i = list->types.size()- 1; i >= 0; i--) {
            AST_FormalRest * formalRest = list->types[i];
            type->add(new ReturnType(formalRest->type));
        }
    }
    type->returnType = new ReturnType(this->type);

    return type;
}
// Handle printing type errors
void typeerror(const char * err, int lineno) {
    //cout << err << endl;
    cout << "Type Violation in Line " << lineno << endl;
    cantContinue = true;
    //exit(-1);
}
void AST_Statement::printDebug() {
    cout << "StatementType: " << type << endl;
    if (type == StatementType::List) {
        cout << "StatementList:" << endl;
        statementList->printDebug();
    }
}
void StatementList::printDebug() {
    cout << "Statement count: " << count << endl;
    for (std::vector<AST_Statement*>::iterator statement = statements.begin() ; statement != statements.end(); statement++) {
        cout << "Statement:" << endl;
        (*statement)->printDebug();
    }
}
void AST_ClassDecl::printDebug() {
    if (simple)
        cout << "ID: " << id << endl;
    else
        cout << "ID: " << id << " extends " << extendsId << endl;
    varDeclList->printDebug();
    methodDeclList->printDebug();
}
void ClassDeclList::printDebug() {
    for (std::vector<AST_ClassDecl*>::iterator classDecl = classDecls.begin() ; classDecl != classDecls.end(); classDecl++) {
        cout << "ClassDecl:" << endl;
        (*classDecl)->printDebug();
    }
}
void AST_VarDecl::printDebug() {
    cout << "VarType: " << varType << endl;
    if (varType == TypeID)
        cout << "id: " << name << endl;
    else
        cout << "type: " << idType << " id: " << name << endl;
}
void VarDeclList::printDebug() {
    cout << count << " variables declared" << endl;
    for (std::vector<AST_VarDecl*>::iterator varDecl = varDecls.begin() ; varDecl != varDecls.end(); varDecl++) {
        cout << "VarDecl:" << endl;
        (*varDecl)->printDebug();
    }
}
void AST_MethodDecl::printDebug() {
    cout << "id: " << id << endl;
    varDeclList->printDebug();
    statementList->printDebug();
    cout << "Return Exp Type: " << returnExp->expression << endl;
}
void MethodDeclList::printDebug() {
    cout << count << " methods declared" << endl;
    for (std::vector<AST_MethodDecl*>::iterator methodDecl = methodDecls.begin() ; methodDecl != methodDecls.end(); methodDecl++) {
        cout << "MethodDecl:" << endl;
        (*methodDecl)->printDebug();
    }
}
void AST_Index::countDepth() {
    if (!recursive)
        depth = 1;
    else {
        depth = 2;
        AST_Index * tmpIndex = index;
        while (tmpIndex->recursive) {
            tmpIndex = tmpIndex->index;
            depth++;
        }
    }
}

//typechecking
ReturnType * AST_Index::typecheck(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl) {
    if (typeSet)
        return type;
    countDepth();
    if (recursive) {
        type = index->typecheck(fn, isClass, mainClass, methodDecl);
        type->arrayDepth = depth;
    }
    else {
        ReturnType * expType = exp->typecheck(fn, isClass, mainClass, methodDecl);
        if (expType == NULL) {
            type = NULL;
            return NULL;
        }
        // type must be a non-array integer
        if (expType->isArray) {
            fn("Index expression is an array", lineno);
            type = NULL;
            typeSet = true;
            return type;
        }
        if (expType->type != PINT) {
            fn("Index expression is not an integer", lineno);
            type = NULL;
            typeSet = true;
            return type;
        }
        type = new ReturnType(PINT, depth);
    }
    typeSet = true;
    return type;
}
ReturnType * AST_Object::typecheck(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl) {
    //real similar to Exp_ObjectCall::typecheck
    SymbolTable * globalTable = isClass ? mainClass->globalTable : methodDecl->parentClass->globalTable;
    switch (type) {
        case NewID: {
           // new Graph()
           // check if Class exists 
           TableRow * classRow = globalTable->getSymbolInfo(id);
            if (classRow == NULL) {
                string base = string("Class ");
                base += id + " does not exist";
                fn(base.c_str(), lineno);
                return NULL;
            }
            return new ReturnType(id, 0);
        }
        case OID: {
            // Graph g; a = g;
            // check if g exists
            if (isClass) {
                TableRow * row = mainClass->symbolTable->getSymbolInfo(id);
                if (row == NULL) {
                    string base = string("Symbol ");
                    base += id + " does not exist";
                    fn(base.c_str(), lineno);
                    return NULL;
                }
                if (row->returnType->type == PVOID || row->returnType->type == PUNKNOWN) {
                    string base = string("Symbol ");
                    base += id + " has an invalid type";
                    fn(base.c_str(), lineno);
                    return NULL;
                }
                return row->returnType;
            }
            else {
                // check if exists in method decl
                TableRow * row = methodDecl->symbolTable->getSymbolInfo(id);
                if (row == NULL) {
                    // check if exists in class decl or inherited class
                    row = methodDecl->parentClass->symbolTable->getSymbolInfo(id);
                    if (row == NULL) {
                        string base = string("Symbol ");
                        base += id + " does not exist";
                        fn(base.c_str(), lineno);
                        return NULL;
                    }
                }
                if (row->returnType->type == PVOID || row->returnType->type == PUNKNOWN) {
                    string base = string("Symbol ");
                    base += id + " has an invalid type";
                    fn(base.c_str(), lineno);
                    return NULL;
                }
                return row->returnType;
            }
        }
        case This: {
            // get current class type
            SymbolTable * classTable = isClass ? mainClass->symbolTable : methodDecl->classTable;
            string className = isClass ? mainClass->id : methodDecl->parentClass->id;
            return new ReturnType(className, 0);
        }
        case NewPrimeType: {
            // new PrimeType Index -> new boolean[5]
            //cout << "Object - New Prime Type Resolve Type Not Implemented" << endl;
            //return new ReturnType();
            ReturnType * indexType = newPrimeType->index->typecheck(fn, isClass, mainClass, methodDecl);
            if (indexType == NULL) {
                fn("Index typecheck is invalid", lineno);
                return NULL;
            }
            switch (newPrimeType->primeType->type) {
                case Int:
                    return new ReturnType(PINT, indexType->arrayDepth);
                case TBool:
                    return new ReturnType(PBOOL, indexType->arrayDepth);
                case TID:
                    return new ReturnType(newPrimeType->primeType->IDValue, indexType->arrayDepth);
            }
        }
    }
    return NULL;
}

//interpretation
ReturnValue * AST_Object::interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke) {
    bool isObjectArray = false;
    switch (type) {
        case OID: {
            if (!isMethod) {
                cout << "Declared object reference within main function, not valid" << endl;
                return NULL;
            }
            // get symbol info for id
            TableRow * symbolInfo = methodInvoke->methodTable->getSymbolInfo(id);
            if (symbolInfo == NULL) {
                symbolInfo = methodInvoke->classTable->getSymbolInfo(id);
            }
            if (symbolInfo == NULL) {
                cout << "Failed to get symbol for " << id << endl;
                return NULL;
            }
            if (symbolInfo->symbolType == SVAR)
                return symbolInfo->varInfo->returnValue;
            else
                return symbolInfo->argInfo->returnValue;
            if (symbolInfo->symbolType == SVAR)
                return symbolInfo->varInfo->returnValue;
            else
                return symbolInfo->argInfo->returnValue;
        }
        case This: {
            if (!isMethod) {
                cout << "this object reference within main function, not valid" << endl;
                return NULL;
            }
            // get current executing class
            SymbolTable * classTable = methodInvoke->method->parentClass->symbolTable;
            string className = methodInvoke->method->parentClass->id;
            ReturnValue * returnValue = new ReturnValue(id);
            returnValue->useThisObject(classTable);
            return returnValue;
        }
        case NewID: {
            // get symbol info
            SymbolTable * globalTable = isMethod ? methodInvoke->method->parentClass->globalTable : mainClass->globalTable;
            TableRow * symbolInfo = globalTable->getSymbolInfo(id);
            if (symbolInfo == NULL) {
                cout << "Failed to get symbol for " << id << endl;
                return NULL;
            }
            // create object
            SymbolTable * classTable = symbolInfo->table;
            ReturnValue * returnValue = new ReturnValue(id);
            returnValue->createObject(classTable);
            return returnValue;
        }
        case NewPrimeType: {
            ReturnValue * indexValue = newPrimeType->index->interpret(isMethod, mainClass, methodInvoke);
            ReturnValue * returnValue;
            switch (newPrimeType->primeType->type) {
                case Int:
                    isObjectArray = false;
                    returnValue = new ReturnValue(1, indexValue->arraySize[0]);
                    break;
                case TBool:
                    isObjectArray = false;
                    returnValue = new ReturnValue(false, indexValue->arraySize[0]);
                    break;
                case TID:
                    isObjectArray = true;
                    returnValue = new ReturnValue(newPrimeType->primeType->IDValue, indexValue->arraySize[0]);
                    break;
            }
            if (indexValue->arraySize[0] == 1) {
                //1d array
                if (isObjectArray)
                    returnValue->createObjectArray(indexValue->arr1[0], 0);
                else
                    returnValue->createArray(indexValue->arr1[0], 0);
            }
            else {
                //2d array
                if (isObjectArray)
                    returnValue->createObjectArray(indexValue->arr1[0], indexValue->arr1[1]);
                else
                    returnValue->createArray(indexValue->arr1[0], indexValue->arr1[1]);
            }
            return returnValue;
        }
    }
    return NULL;
}
ReturnValue * AST_Index::interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke) {
    //[1][1]
    int indices[depth];
    ReturnValue * expValue = exp->interpret(isMethod, mainClass, methodInvoke);
    if (recursive) {
        indices[1] = expValue->intValue;
        indices[0] = index->exp->interpret(isMethod, mainClass, methodInvoke)->intValue;
    }
    else
        indices[0] = expValue->intValue;
    ReturnValue * value = new ReturnValue(0, 1);
    value->createArray(depth);
    for (int i = 0; i < depth; i++) {
        value->arr1[i] = indices[i];
    }
    return value;
}

const char * pB(int value) {
    if (value == 1)
        return "FALSE";
    else if (value == 0) 
        return "TRUE";
    return "ERR";
}
//fix escape characters within string literal
//Fixes \n, \t, \", "\\", \b
string fixLiteral(string value) {
    string copy = string();
    for (int i = 0; i < value.length(); i++) {
        if (value[i] == '\\' && i + 1 < value.length()) {
            char next = value[i+1];
            switch (next) {
                case 'n':
                    copy.push_back('\n');
                    break;
                case 't':
                    copy.push_back('\t');
                    break;
                case '"':
                    copy.push_back('"');
                    break;
                case '\\':
                    copy.push_back('\\');
                    break;
                case 'b':
                    copy.push_back('\b');
                    break;
                default:
                    copy.push_back(value[i]);
                    copy.push_back(next);
            }
            i++;
        }
        else {
            copy.push_back(value[i]);
        }
    }
    return copy;
}
PType fromStoredType(StoredType type) {
    switch (type) {
        case Int:
            return PType::PINT;
        case TBool:
            return PType::PBOOL;
        case TID:
            return PType::POBJECT;
        default:
            return PType::PUNKNOWN;
    }
}
void addVarDecl(void (*fn)(const char * err, int lineno), AST_VarDecl* varDecl, SymbolTable * symbolTable, int lineno) {
    switch (varDecl->varType) {
        case TypeID:
            // int a || int[] a || Graph[a]
            if (!symbolTable->addVar(varDecl->name, new AST_Node(varDecl), new ReturnType(varDecl->type), symbolTable,varDecl->type->arrayDepth)) {
                string s = string("Failed to add vardecl id: ");
                s += varDecl->name + ", type: " + varDecl->idType + ". Variable name already exists.";
                fn(s.c_str(), lineno);
            }
            break;
        case IDID:
            // Compute compute
            if (!symbolTable->addVar(varDecl->name, new AST_Node(varDecl), new ReturnType(varDecl->idType, 0), symbolTable, 0)) {
                string s = string("Failed to add vardecl id: ");
                s += varDecl->name + ", type: " + varDecl->idType + ". Variable name already exists.";
                fn(s.c_str(), lineno);
            }
            break;
        default:
            cout << "VarDecl has invalid vartype" << endl;
            exit(-1);
    }
}
void addArg(void (*fn)(const char * err, int lineno), AST_FormalRest* formalRest, SymbolTable * symbolTable, int lineno) {
    // int a || int[] a || Graph[a]
    if (!symbolTable->addArg(formalRest->id, new AST_Node(formalRest), new ReturnType(formalRest->type), symbolTable)) {
        string s = string("Failed to add arg id: ");
        s += formalRest->id + ", type: " + ". Arg name already exists.";
        fn(s.c_str(), lineno);
    }
}
void addMethod(void (*fn)(const char * err, int lineno), string className, AST_MethodDecl* methodDecl, SymbolTable * symbolTable, int lineno) {
    if (!symbolTable->addMethod(methodDecl->id, className, new AST_Node(methodDecl), 
        methodDecl->getMethodType(), symbolTable, methodDecl->symbolTable)) {
            string s = string("Failed to add method ");
                className + "::" + methodDecl->id + ". Variable name already exists.";
                fn(s.c_str(), lineno);
    }
}