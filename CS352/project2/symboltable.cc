#include "ast.hh"

//enum cout print
std::ostream& operator<<(std::ostream& out, const PType value){
    switch(value) {
        case PINT:
            return out << "PINT";
        case PBOOL:
            return out << "PBOOL";
        case POBJECT:
            return out << "POBJECT";
        case PSTRING:
            return out << "PSTRING";
        case PVOID:
            return out << "PVOID";
        case PUNKNOWN:
            return out << "PUNKNOWN";
        default:
            return out << "UNKNOWN";
    }
}
std::ostream& operator<<(std::ostream& out, const SType value){
    switch(value) {
        case SCLASS:
            return out << "SCLASS";
        case SVAR:
            return out << "SVAR";
        case SARG:
            return out << "SARG";
        case SMETHOD:
            return out << "SMETHOD";
        case SUNKNOWN:
            return out << "SUNKNOWN";
        default:
            return out << "UNKNOWN";
    }
}
// Shitty check to see if class::Method contains Method and not Method2
bool SymbolTable::methodIsName(string symbol, string method) {
    int lastIndex = 0;
    for (int i = 0; i < symbol.length(); i++) {
        if (symbol[i] == ':')
            lastIndex = i;
    }
    int relativeLength = symbol.length() - lastIndex - 1;
    if (relativeLength == method.length())
        return true;
    else
        return false;
}
ReturnType::ReturnType(AST_Type * type) {
    this->isArray = type->isArray;
    this->arrayDepth = type->arrayDepth;
    switch (type->primeType->type) {
        case Int:
            this->type = PINT;
            break;  
        case TBool:
            this->type = PBOOL;
            break;
        case TID:
            this->type = POBJECT;
            this->objectID = type->primeType->IDValue;
            break;
    }
}
ReturnType::ReturnType(AST_FormalRest * formalRest) {
    ReturnType(formalRest->type);
}
void ReturnValue::createArray(int size1, int size2) {
    isArray = true;
    arraySize[0] = size1;
    arraySize[1] = size2;
    //set array depth you tard
    arrayDepth = returnType->arrayDepth;

    if (arrayDepth == 1)
        arr1 = (int*)malloc(sizeof(int) * size1);
    else if (arrayDepth == 2) {
        arr2 = (int**)malloc(sizeof(int*) * size1);
        for (int i = 0; i < size1; i++) {
            arr2[i] = (int*)malloc(sizeof(int) * size2);
        }
    }
    else {
        cout << "Can only handle 2D arrays" << endl;
        return;
    }
    fillArray();
}
void ReturnValue::createObjectArray(int size1, int size2) {
    isObjectArray = true;
    arraySize[0] = size1;
    arraySize[1] = size2;
    arrayDepth = returnType->arrayDepth;

    if (arrayDepth == 1)
        objArr1 = (ReturnValue**)malloc(sizeof(ReturnValue*) * size1);
    else if (arrayDepth == 2) {
        objArr2 = (ReturnValue***)malloc(sizeof(ReturnValue**) * size1);
        for (int i = 0; i < size1; i++) {
            objArr2[i] = (ReturnValue**)malloc(sizeof(ReturnValue*) * size2);
        }
    }
    else {
        cout << "Can only handle 2D arrays" << endl;
        return;
    }
    fillArray();
}
void ReturnValue::createObject(SymbolTable * classTable) {
    isObject = true;
    initialized = true;
    this->classTable = new SymbolTable(*classTable, true);
    this->classTable = this->classTable;
}
void ReturnValue::fillArray() {
    if (!isObjectArray) {
        if (arrayDepth == 1) {
            for (int i = 0; i < arraySize[0]; i++) {
                arr1[i] = 0;
            }
        }
        else if (arrayDepth == 2) {
            for (int i = 0; i < arraySize[0]; i++) {
                for (int j = 0; j < arraySize[1]; j++) {
                    arr2[i][j] = 0;
                }
            }
        }
        else {
            cout << "Can only handle 2D arrays" << endl;
            return;
        }
    }
    else {
        if (arrayDepth == 1) {
            for (int i = 0; i < arraySize[0]; i++) {
                objArr1[i] = NULL;
            }
        }
        else if (arrayDepth == 2) {
            for (int i = 0; i < arraySize[0]; i++) {
                for (int j = 0; j < arraySize[1]; j++) {
                    objArr2[i][j] = NULL;
                }
            }
        }
        else {
            cout << "Can only handle 2D arrays" << endl;
            return;
        }
    }
}
bool ReturnType::equal(ReturnType * other) {
    if (other == NULL)
        return false;
    if (isArray != other->isArray)
        return false;
    if (arrayDepth != other->arrayDepth)
        return false;
    if (type != other->type)
        return false;
    if (type == POBJECT && (objectID != other->objectID))
        return false;
    return true;
}
bool SymbolTable::addVar(string name, AST_Node * node, ReturnType * returnType, SymbolTable * table, int arrayDepth) {
    if (symbolExists(name)) {
        cout << "Symbol already exists in table" << endl;
        return false;
    }
    TableRow * row = new TableRow(name, SType::SVAR, returnType, node, table);
    /*switch (returnType) {
        case PINT:
            row->addVarInfo(new VarInfo(1, arrayDepth));
            break;
        case PBOOL:
            row->addVarInfo(new VarInfo(true, arrayDepth));
            break;
        case POBJECT:
            row->addVarInfo(new VarInfo(node->astVarDecl->idType, arrayDepth));
            break;
        default:
            cout << "Invalid argument type, can't add to symbol table" << endl;
            return false;
    }*/
    row->addVarInfo(new VarInfo(returnType));
    rows.push_back(row);
    symbolCount++;
    return true;
}
bool SymbolTable::addMethod(string name, string className, AST_Node * node, MethodType * methodType, SymbolTable * table, SymbolTable * methodTable) {
    string fixedName = methodName(name, className);
    if (symbolExists(fixedName)) {
        // symbol already exists, but allow overloaded methods
        TableRow * row = getSymbolInfo(fixedName);
        if (row != NULL && row->methodInfo->methodType == methodType) {
            cout << "Symbol already exists in table" << endl;
            return false;
        }
    }
    TableRow * row = new TableRow(fixedName, SType::SMETHOD, methodType->returnType, node, table);
    row->addMethodInfo(new MethodInfo(methodTable, methodType));
    rows.push_back(row);
    symbolCount++;
    return true;
}
bool SymbolTable::addClass(string name, AST_Node * node, SymbolTable * table, bool mainClass) {
    if (symbolExists(name)) {
        cout << "Symbol already exists in table" << endl;
        return false;
    }
    TableRow * row = new TableRow(name, SType::SCLASS, new ReturnType(PVOID, 0), node, table);
    row->addClassInfo(new ClassInfo(mainClass));
    rows.push_back(row);
    symbolCount++;
    return true;
}
bool SymbolTable::addArg(string name, AST_Node * node, ReturnType * returnType, SymbolTable * table) {
    if (symbolExists(name)) {
        cout << "Symbol already exists in table" << endl;
        return false;
    }
    TableRow * row = new TableRow(name, SType::SARG, returnType, node, table);
    /*switch (returnType) {
        case PINT:
            row->addArgInfo(new ArgInfo(1));
            break;
        case PBOOL:
            row->addArgInfo(new ArgInfo(true));
            break;
        case POBJECT:
            row->addArgInfo(new ArgInfo(node->astFormalRest->type->primeType->IDValue));
            break;
        default:
            cout << "Invalid argument type, can't add to symbol table" << endl;
            return false;
    }*/
    row->addVarInfo(new VarInfo(returnType));
    rows.push_back(row);
    symbolCount++;
    return true;
}
bool SymbolTable::symbolExists(string name) {
    if (symbolCount == 0)
        return false;
    for (vector<TableRow*>::iterator row = rows.begin(); row != rows.end(); row++) {
        if ((*row)->symbol == name)
            return true;
    }
    return false;
}
bool SymbolTable::updateSymbolTable(string name, SymbolTable * table) {
    if (symbolCount == 0)
        return false;
    for (vector<TableRow*>::iterator row = rows.begin(); row != rows.end(); row++) {
        if ((*row)->symbol == name) {
            (*row)->table = table;
            return true;
        }
    }
    return false;
}
bool SymbolTable::updateSymbolInfo(string symbol, VarInfo * info) {
    for (vector<TableRow*>::iterator row = rows.begin(); row != rows.end(); row++) {
        if ((*row)->symbol == symbol) {
            //delete (*row)->varInfo;
            (*row)->varInfo = info;
            return true;
        }
    }
    if (inheritedTable != NULL) {
        for (vector<TableRow*>::iterator row = inheritedTable->rows.begin(); 
        row != inheritedTable->rows.end(); row++) {
            if ((*row)->symbol == symbol) {
                //delete (*row)->varInfo;
                (*row)->varInfo = info;
                return true;
            }
        }
    }
    return false;
}
bool SymbolTable::updateSymbolInfo(string symbol, ArgInfo * info) {
    for (vector<TableRow*>::iterator row = rows.begin(); row != rows.end(); row++) {
        if ((*row)->symbol == symbol) {
            //delete (*row)->argInfo;
            (*row)->argInfo = info;
            return true;
        }
    }
    if (inheritedTable != NULL) {
        for (vector<TableRow*>::iterator row = inheritedTable->rows.begin(); 
        row != inheritedTable->rows.end(); row++) {
            if ((*row)->symbol == symbol) {
                //delete (*row)->argInfo;
                (*row)->argInfo = info;
                return true;
            }
        }
    }
    return false;
}
// Gets the table row object for a symbol, null if the symbol doesn't exist
TableRow * SymbolTable::getSymbolInfo(string name) {
    for (vector<TableRow*>::iterator row = rows.begin(); row != rows.end(); row++) {
        if ((*row)->symbol == name) {
            TableRow * tr = (*row);
            return tr;
        }
    }
    if (inheritedTable != NULL) {
        for (vector<TableRow*>::iterator row = inheritedTable->rows.begin(); 
        row != inheritedTable->rows.end(); row++) {
            if ((*row)->symbol == name) {
                TableRow * tr = (*row);
                return tr;
            }
        }
    }
    return NULL;
}
TableRow * SymbolTable::getSymbolInfo(string name, SymbolTable * extendedTable) {
    cout << "\n\nUsing extended getSymbolInfo\n\n";
    TableRow * firstSearch = getSymbolInfo(name);
    if (firstSearch == NULL) {
        //search in the extendedTable
        return extendedTable->getSymbolInfo(name);
    }
    else {
        return firstSearch;
    }
}
TableRow * SymbolTable::getMethodInfo(string name) {
    // search the symbol table ignoring the class precendece
    for (vector<TableRow*>::iterator row = rows.begin(); row != rows.end(); row++) {
        if ((*row)->symbolType == SMETHOD) {
            // check if the method exists within the symbol
            TableRow * rowDebug = (*row);
            if ((*row)->symbol.find(name) != string::npos && methodIsName((*row)->symbol, name)) {
                return (*row);
            }
        }
    }
    if (inheritedTable != NULL) {
        for (vector<TableRow*>::iterator row = inheritedTable->rows.begin(); 
        row != inheritedTable->rows.end(); row++) {
            if ((*row)->symbolType == SMETHOD) {
                // check if the method exists within the symbol
                TableRow * rowDebug = (*row);
                if ((*row)->symbol.find(name) != string::npos && methodIsName((*row)->symbol, name)) {
                    return (*row);
                }
            }
        }
    }
    return NULL;
}
void ArgInfo::printDebug() {
    //cout << "\tReturn Type: " << returnType << endl;
    cout << "\tType: " << returnValue->returnType->type << ", isArray: " << returnValue->returnType->isArray << ", arrayDepth: " << returnValue->returnType->arrayDepth;
    if (returnValue->returnType->type == POBJECT)
        cout << ", Type ID: " << returnValue->returnType->objectID;
    cout << endl;
}
string MethodType::argToString() {
    string base = string("[");
    for (int i = 0; i < argTypes.size(); i++) {
        switch(argTypes[i]->type) {
            case PINT:
                base +=  "PINT";
                break;
            case PBOOL:
                base +=  "PBOOL";
                break;
            case POBJECT:
                base +=  argTypes[i]->objectID;
                break;
            case PSTRING:
                base +=  "PSTRING";
                break;
            case PVOID:
                base +=  "PVOID";
                break;
            case PUNKNOWN:
                base +=  "PUNKNOWN";
                break;
            default:
                base += "UNKNOWN";
            if (argTypes[i]->isArray) {
                string arr = string("[");
                arr += argTypes[i]->arrayDepth + "]";
                base += arr;
            }
        }
        if (i < argTypes.size() - 1) {
            base += ", ";
        }
    }
    base += "]";
    return base;
}
void MethodInfo::printDebug() {
    cout << "\tCall Table: " << &callTable << ", ReturnType: " << methodType->returnType->type << ", ArgTypes: " <<
    methodType->argToString() << endl;
}
void VarInfo::printDebug() {
    cout << "\tReturn Type: " << returnValue->returnType->type << ", arrayDepth: " << returnValue->returnType->arrayDepth << endl;
}
void ClassInfo::printDebug() {
    cout << "\tMain Class: " << mainClass << endl;
}
void SymbolTable::printDebug() {
    cout << "Symbol Count: " << symbolCount << endl;
    cout << "#: Symbol, SymbolType, ReturnType, Node, Table, info" << endl;
    for (int i = 0; i < symbolCount; i++) {
        TableRow * row = rows[i];
        cout << i << ": " << row->symbol << ", " << row->symbolType << ", " << row->returnType <<
        ", " << &row->node << ", " << &row->table << endl;
        switch (row->symbolType) {
            case SCLASS:
                row->classInfo->printDebug();
                break;
            case SVAR:
                row->varInfo->printDebug();
                break;
            case SARG:
                row->argInfo->printDebug();
                break;
            case SMETHOD:
                row->methodInfo->printDebug();
            default:
                break;
        }
    }
}

MethodInvoke::MethodInvoke(AST_MethodDecl * method, vector<ArgumentTuple*> * args, ReturnValue * object) {
    this->method = method;
    this->methodTable = new SymbolTable(*(method->symbolTable), false);
    //this->classTable = method->parentClass->symbolTable;
    // get object's class table
    this->classTable = object->classTable;
    this->methodName = method->id;
    // resolve arguments
    this->argValues = argValues;
    for (vector<ArgumentTuple*>::iterator arg = args->begin(); arg != args->end(); arg++) {
        TableRow * argRow = methodTable->getSymbolInfo((*arg)->name);
        if (argRow == NULL) {
            cout << "MethodInvoke failed to get table info for argument " << (*arg)->name << endl;
        }
        else {
            argRow->argInfo->returnValue = (*arg)->value;
            argRow->table = methodTable;
        }
    }
}
ReturnValue * MethodInvoke::invoke(bool isMethod, string methodName) {
    // run method
    ReturnValue * statementResult = method->statementList->interpret(true, NULL, this);
    ReturnValue * returnResult;

    if (statementResult == NULL) {
        returnResult = method->returnExp->interpret(true, NULL, this);
    }
    //update symbol tables
    if (isMethod) {
        // check if we're making a recursive call
        if (methodName == this->methodName) {
            // don't update the table
        }
        else {
            method->symbolTable = this->methodTable;
        }
    }
    else {
        method->symbolTable = this->methodTable;
    }
    if (statementResult != NULL) {
        return statementResult;
    }
    return returnResult;
}