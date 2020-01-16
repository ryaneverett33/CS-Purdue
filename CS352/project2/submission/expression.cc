#include "ast.hh"
#include "symboltable.hh"

/*PType AST_Exp::resolveType(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl) {
    if (resolvedType)
        return type;
    switch (expression) {
        case Expression::Binary:
            type = binaryOp->resolveType(fn, isClass, mainClass, methodDecl);
            break;
        case Expression::Unary:
            type = unaryOp->resolveType(fn, isClass, mainClass, methodDecl);
            break;
        case Expression::Index:
            type = index->resolveType(fn, isClass, mainClass, methodDecl);
            break;
        case Expression::Parens:
            type = parens->resolveType(fn, isClass, mainClass, methodDecl);
            break;
        case Expression::Length:
        case Expression::IndexLength:
        case Expression::INT_LITERAL:
            type = PType::PINT;
            break;
        case Expression::EBool:
            type = PType::PBOOL;
            break;
        case Expression::Object:
            cout << "Exp:Object Should check if object exists first" << endl;
            type = PType::POBJECT;
            break;
        case Expression::ObjectCall:
            type = objectCall->resolveType(fn, isClass, mainClass, methodDecl);
            break;
        default:
            cout << "Unable to resolve type, unknown expression type" << endl;
            type = PType::PUNKNOWN;
    }
    resolvedType = true;
    return type;
}*/

// Interpretation
ReturnValue * AST_Exp::interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke) {
    switch (expression) {
        case Expression::Binary:
            return binaryOp->interpret(isMethod, mainClass, methodInvoke);
        case Expression::Unary:
            return unaryOp->interpret(isMethod, mainClass, methodInvoke);
        case Expression::Index:
            return index->interpret(isMethod, mainClass, methodInvoke);
        case Expression::Parens:
            return parens->interpret(isMethod, mainClass, methodInvoke);
        case Expression::Length:
            return length->interpret(isMethod, mainClass, methodInvoke);
        case Expression::IndexLength:
            return indexLength->interpret(isMethod, mainClass, methodInvoke);
        case Expression::INT_LITERAL:
            return new ReturnValue(intLiteral);
        case Expression::EBool:
            return new ReturnValue(boolLiteral);
        case Expression::Object:
            return object->interpret(isMethod, mainClass, methodInvoke);
        case Expression::ObjectCall:
            return objectCall->interpret(isMethod, mainClass, methodInvoke);
    }
    return NULL;
}
// Interpretation
ReturnValue * Exp_BinaryOp::interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke) {
    ReturnValue * leftValue = left->interpret(isMethod, mainClass, methodInvoke);
    ReturnValue * rightValue = right->interpret(isMethod, mainClass, methodInvoke);
    //boolean -> boolean operations
    if (op.compare("&&") == 0 || op.compare("||") == 0) {
        if (op.compare("&&") == 0)
            return new ReturnValue(leftValue->boolValue && rightValue->boolValue);
        else
            return new ReturnValue(leftValue->boolValue || rightValue->boolValue);
    }
    //boolean, int -> boolean operations
    else if (op.compare("==") == 0 || op.compare("!=") == 0) {
        if (left->type->type == PType::PBOOL) {
            if (op.compare("==") == 0)
                return new ReturnValue(leftValue->boolValue == rightValue->boolValue);
            else
                return new ReturnValue(leftValue->boolValue != rightValue->boolValue);
        }
        else {
            if (op.compare("==") == 0)
                return new ReturnValue(leftValue->intValue == rightValue->intValue);
            else
                return new ReturnValue(leftValue->intValue != rightValue->intValue);
        }
    }
    //int -> boolean operations
    else if (op.compare("<") == 0 || op.compare(">") == 0 || op.compare("<=") == 0 || op.compare(">=") == 0) {
        if (op.compare("<") == 0)
            return new ReturnValue(leftValue->intValue < rightValue->intValue);
        else if (op.compare(">") == 0)
            return new ReturnValue(leftValue->intValue > rightValue->intValue);
        else if (op.compare("<=") == 0)
            return new ReturnValue(leftValue->intValue <= rightValue->intValue);
        else
            return new ReturnValue(leftValue->intValue >= rightValue->intValue);
    }
    //int -> int operations
    else if (op.compare("+") == 0 || op.compare("-") == 0 || op.compare("*") == 0 || op.compare("/") == 0) {
        if (op.compare("+") == 0)
            return new ReturnValue(leftValue->intValue + rightValue->intValue);
        else if (op.compare("-") == 0)
            return new ReturnValue(leftValue->intValue - rightValue->intValue);
        else if (op.compare("*") == 0)
            return new ReturnValue(leftValue->intValue * rightValue->intValue);
        else
            return new ReturnValue(leftValue->intValue / rightValue->intValue);
    }
    else {
        cout << "Unable to interpret binary op, unknown operator" << endl;
        return NULL;
    }
}
ReturnValue * Exp_Parens::interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke) {
    return exp->interpret(isMethod, mainClass, methodInvoke);
}
ReturnValue * Exp_UnaryOp::interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke) {
    ReturnValue * value = exp->interpret(isMethod, mainClass, methodInvoke);
    switch (op) {
        case '!':
            if (value->returnType->type == PBOOL) {
                value->intValue = !value->boolValue;
                return value;
            }
            else {
                value->intValue = !value->intValue;
                return value;
            }
        case '+':
            return value;
        case '-':
            value->intValue = value->intValue * -1;
            return value;
    }
    return NULL;
}
ReturnValue * Exp_ObjectCall::interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke) {
    ReturnValue * objectValue = object->interpret(isMethod, mainClass, methodInvoke);
    if (objectValue == NULL) {
        cout << "Failed to interpret object" << endl;
        return NULL;
    }
    /*switch (object->type) {
        case NewID: {
            // new Object().call()
            // get method from classTable
            break;
        }
        case OID: {
            // Object o; o.call();
            // get o info
            if (!isMethod) {
                cout << "Object Call on object reference within main function, not valid" << endl;
                return NULL;
            }
            TableRow * variableInfo = methodInvoke->methodTable->getSymbolInfo(object->id);
            if (variableInfo == NULL)
                variableInfo = methodInvoke->classTable->getSymbolInfo(object->id);
            if (variableInfo == NULL) {
                cout << "Failed to get symbol for " << object->id << endl;
                return NULL;
            }
            symbolInfo = variableInfo->table->getMethodInfo(id);
            break;
        }
        case This: {
            // this.call()
            if (!isMethod) {
                cout << "Object Call on this while within main function, not valid" << endl;
                return NULL;
            }
            symbolInfo = methodInvoke->classTable->getMethodInfo(id);
            break;
        }
        case NewPrimeType: {
            // this can't happen
            cout << "Object Call on new PrimeType, not valid" << endl;
            return NULL;
        }
    }*/
    TableRow * symbolInfo = objectValue->classTable->getMethodInfo(id);
    if (symbolInfo == NULL || symbolInfo->symbolType != SMETHOD) {
        cout << "Failed to get method info for invocation" << endl;
        return NULL;
    }

    AST_MethodDecl * methodDecl = symbolInfo->node->astMethodDecl;
    // resolve arguments
    vector<ArgumentTuple*> * args = new vector<ArgumentTuple*>();
    /*
        Argument names are in backwards order
        Values are in forwards order
        Start considering different majors
    */
    int valueIndex = 0;
    for (int i = methodDecl->list->count-1; i >= 0; i--) {
        ReturnValue * value = expList->exps[valueIndex]->interpret(isMethod, mainClass, methodInvoke);
        string argName = methodDecl->list->types[i]->id;
        args->push_back(new ArgumentTuple(value, argName));
        valueIndex++;
    }
    MethodInvoke *invoke = new MethodInvoke(methodDecl, args, objectValue);
    return invoke->invoke(isMethod, isMethod ? methodInvoke->methodName : string());
}
ReturnValue * Exp_Index::interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke) {
    //id[index]
    if (!isMethod) {
        cout << "Variable reference within main class, invalid" << endl;
        return NULL;
    }
    ReturnValue * indexValue = index->interpret(isMethod, mainClass, methodInvoke);
    TableRow * symbolInfo = methodInvoke->methodTable->getSymbolInfo(id);
    if (symbolInfo == NULL) {
        symbolInfo = methodInvoke->classTable->getSymbolInfo(id);
    }
    if (symbolInfo == NULL) {
        cout << "Failed to get symbol for " << id << endl;
        return NULL;
    }
    ReturnValue * symbolData = (symbolInfo->symbolType == SVAR ? symbolInfo->varInfo->returnValue : symbolInfo->argInfo->returnValue);
    if (symbolData->returnType->type == PBOOL) {
        if (symbolData->arrayDepth == 1)
            return new ReturnValue((bool)symbolData->arr1[indexValue->arr1[0]]);
        else
            return new ReturnValue((bool)symbolData->arr2[indexValue->arr1[0]][indexValue->arr1[1]]);
    }
    else if (symbolData->returnType->type == PINT) {
        if (symbolData->arrayDepth == 1)
            return new ReturnValue(symbolData->arr1[indexValue->arr1[0]]);
        else
            return new ReturnValue(symbolData->arr2[indexValue->arr1[0]][indexValue->arr1[1]]);
    }
    else if (symbolData->returnType->type == POBJECT) {
        if (symbolData->arrayDepth == 1)
            return symbolData->objArr1[indexValue->arr1[0]];
        else
            return symbolData->objArr2[indexValue->arr1[0]][indexValue->arr1[1]];
    }
    return NULL;
}
ReturnValue * Exp_IndexLength::interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke) {
    // id[0].length
    //get symbol info
    if (!isMethod) {
        cout << "Referenced an id within the main class, not allowed" << endl;
        return NULL;
    }
    TableRow * symbolInfo = methodInvoke->methodTable->getSymbolInfo(id);
    if (symbolInfo == NULL) {
        symbolInfo = methodInvoke->classTable->getSymbolInfo(id);
    }
    if (symbolInfo == NULL) {
        cout << "Failed to get symbol for " << id << endl;
        return NULL;
    }
    // array of index values e.g. [1][2] - > [1,2]
    ReturnValue * indexValue = index->interpret(isMethod, mainClass, methodInvoke);
    if (indexValue->arraySize[0] > 1) {
        cout << "IndexLength only supports 2D arrays" << endl;
        return NULL;
    }
    ReturnValue * value;
    if (symbolInfo->symbolType == SVAR)
        value = symbolInfo->varInfo->returnValue;
    else
        value = symbolInfo->argInfo->returnValue;
    
    return new ReturnValue(value->arraySize[1]);
}
ReturnValue * Exp_Length::interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke) {
    // length of first dimension
    // id.length
    // get symbol info for id
    if (!isMethod) {
        cout << "Referenced an id within the main class, not allowed" << endl;
        return NULL;
    }
    TableRow * symbolInfo = methodInvoke->methodTable->getSymbolInfo(id);
    if (symbolInfo == NULL) {
        symbolInfo = methodInvoke->classTable->getSymbolInfo(id);
    }
    if (symbolInfo == NULL) {
        cout << "Failed to get symbol for " << id << endl;
        return NULL;
    }
    ReturnValue * value;
    if (symbolInfo->symbolType == SVAR)
        value = symbolInfo->varInfo->returnValue;
    else
        value = symbolInfo->argInfo->returnValue;
    
    return new ReturnValue(value->arraySize[0]);
}

// Typechecking
ReturnType * Exp_BinaryOp::typecheck(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl) {
    ReturnType * leftType = left->typecheck(fn, isClass, mainClass, methodDecl);
    ReturnType * rightType = right->typecheck(fn, isClass, mainClass, methodDecl);
    if (leftType == NULL || rightType == NULL)
        return NULL;
    if (!leftType->equal(rightType)) {
        fn("Binary Op, types don't match", lineno);
        return NULL;
    }
    //boolean -> boolean operations
    if (op.compare("&&") == 0 || op.compare("||") == 0) {
        if (leftType->type != PBOOL) {
            fn("Binary Op, type is not a boolean", lineno);
            return NULL;
        }
        return new ReturnType(PBOOL, 0);
    }
    //int, boolean -> boolean
    else if (op.compare("==") == 0 || op.compare("!=") == 0) {
        if (leftType->type != PBOOL && leftType->type != PINT) {
            fn("Binary Op, type is not a boolean or integer", lineno);
            return NULL;
        }
        if (leftType->isArray) {
            fn("Binary Op, type is an array", lineno);
            return NULL;
        }
        return new ReturnType(PBOOL, 0);
    }
    //int -> boolean operations
    else if (op.compare("<") == 0 || op.compare(">") == 0 || op.compare("<=") == 0 || op.compare(">=") == 0) {
        if (leftType->type != PType::PBOOL && leftType->type != PType::PINT) {
            fn("Binary Op, type is not a boolean or integer", lineno);
            return NULL;
        }
        if (leftType->isArray) {
            fn("Binary Op, type is an array", lineno);
            return NULL;
        }
            
        return new ReturnType(PBOOL, 0);
    }
    //int -> int operations
    else if (op.compare("+") == 0 || op.compare("-") == 0 || op.compare("*") == 0 || op.compare("/") == 0) {
        if (leftType->type != PType::PINT) {
            fn("Binary Op, type is not an integer", lineno);
            return NULL;
        }
        if (leftType->isArray) {
            fn("Binary Op, type is an array", lineno);
            return NULL;
        }
        return new ReturnType(PINT, 0);
    }
    else {
        return NULL;
    }
}
ReturnType * Exp_UnaryOp::typecheck(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl) {
    // op: ! Exp (->bool), + (->int), - (->int)
    ReturnType * type = exp->typecheck(fn, isClass, mainClass, methodDecl);
    if (type == NULL)
        return NULL;
    if (type->type != PType::PINT && type->type != PType::PBOOL) {
        fn("Unary Op, type is not an integer or boolean", lineno);
        return NULL;
    }
    if (type->isArray) {
        fn("Unary Op, type is an array", lineno);
        return NULL;
    }
        
    if (type->type == PType::PBOOL && op != '!') {
        string base = string("Unary Op, invalid operation ");
        base += op + " on boolean type";
        fn(base.c_str(), lineno);
        return NULL;
    }
    return type;
}
ReturnType * Exp_Index::typecheck(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl) {
    // get symbol info
    TableRow * symbolInfo;
    if (isClass)
        symbolInfo = mainClass->symbolTable->getSymbolInfo(id);
    else {
        // check if local var first
        symbolInfo = methodDecl->symbolTable->getSymbolInfo(id);
        if (symbolInfo == NULL) {
            // check if in class
            symbolInfo = methodDecl->parentClass->symbolTable->getSymbolInfo(id);
        }
    }
    if (symbolInfo == NULL) {
        string base = string("Symbol ");
        base += id + " does not exist";
        fn(base.c_str(), lineno);
        return NULL;
    }
    // check that symbol is an array
    if (symbolInfo->symbolType != SVAR && symbolInfo->symbolType != SARG) {
        string base = string("Symbol ");
        base += id + " is not a variable";
        fn(base.c_str(), lineno);
        return NULL;
    }
    if (!symbolInfo->returnType->isArray) {
        string base = string("Symbol ");
        base += id + " is not an array";
        fn(base.c_str(), lineno);
        return NULL;
    }
    // check that index is an integer
    ReturnType * indexType = index->typecheck(fn, isClass, mainClass, methodDecl);
    if (indexType == NULL || indexType->type != PINT) {
        string base = string("Index expression for ");
        base += id + " is invalid";
        fn(base.c_str(), lineno);
        return NULL;
    }
    if (index->depth != symbolInfo->returnType->arrayDepth) {
        cout << "Index depth: " << index->depth << ", symbol depth: " << symbolInfo->returnType->arrayDepth << endl;
        string base = string("Index is invalid depth for ");
        base += id;
        fn(base.c_str(), lineno);
        return NULL;
    }
    ReturnType * type = new ReturnType(symbolInfo->returnType->type);
    if (type->type == POBJECT)
        type->objectID = symbolInfo->returnType->objectID;
    return type;
}
ReturnType * Exp_Parens::typecheck(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl) {
    return exp->typecheck(fn, isClass, mainClass, methodDecl);
}
ReturnType * Exp_ObjectCall::typecheck(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl) {
    // check if method exists
    // return method type
    SymbolTable * globalTable = isClass ? mainClass->globalTable : methodDecl->parentClass->globalTable;
    switch (object->type) {
        case NewID: {
            // new Object().call() 
            // check if Object is a valid Class
            // check if call is a valid method
            TableRow * classRow = globalTable->getSymbolInfo(object->id);
            if (classRow == NULL) {
                string base = string("Class ");
                base += object->id + " does not exist";
                fn(base.c_str(), lineno);
                return NULL;
            }
            else {
                if (classRow->symbolType != SCLASS) {
                    string base = string("Symbol ");
                    base += object->id + " is not a class";
                    fn(base.c_str(), lineno);
                    return NULL;
                }
                SymbolTable * classTable = classRow->table;
                TableRow * methodRow;
                methodRow = classTable->getMethodInfo(id);
                if (methodRow == NULL) {
                    string base = string("Method ");
                    base += id + " does not exist in class " + object->id;
                    fn(base.c_str(), lineno);
                    return NULL;
                }
                else {
                    MethodType * methodType = methodRow->methodInfo->methodType;
                    if (methodType->count != expList->count) {
                        fn("Method call arguments are incorrect", lineno);
                        return NULL;
                    }
                    else {
                        // check argument types
                        for (int i = 0; i < methodType->count; i++) {
                            AST_Exp * exp = expList->exps[i];
                            ReturnType * expType = exp->typecheck(fn, isClass, mainClass, methodDecl);
                            if (!expType->equal(methodType->argTypes[i])) {
                                string base = string("Method call argument at position ");
                                base += i + " differs from definition";
                                fn(base.c_str(), lineno);
                                return NULL;
                            }
                        }
                        return methodType->returnType;
                    }
                }
            }
            break;
        }
        case OID: {
            // Graph graph; graph.call() 
            // check if variable graph exists
            // check if call is a valid method
            TableRow * variable;
            if (isClass) {
                variable = mainClass->symbolTable->getSymbolInfo(object->id);
                if (variable == NULL) {
                    string base = string("Symbol ");
                    base += object->id + " does not exist";
                    fn(base.c_str(), lineno);
                    return NULL;
                }
            }
            else {
                // check if within local scope first
                variable = methodDecl->symbolTable->getSymbolInfo(object->id);
                if (variable == NULL) {
                    // check if in class definition or in inherited class
                    variable = methodDecl->parentClass->symbolTable->getSymbolInfo(object->id);
                    if (variable == NULL) {
                        string base = string("Symbol ");
                        base += object->id + " does not exist";
                        fn(base.c_str(), lineno);
                        return NULL;
                    }
                }
            }
            // check if call is a valid method for the variable
            if (variable->returnType->type != POBJECT) {
                string base = string("Symbol ");
                base += object->id + " is not an object";
                fn(base.c_str(), lineno);
                return NULL;
            }
            string className = variable->returnType->objectID;
            TableRow * classRow = globalTable->getSymbolInfo(className);
            if (classRow == NULL) {
                string base = string("Class ");
                base += object->id + " does not exist";
                fn(base.c_str(), lineno);
                return NULL;
            }
            else {
                if (classRow->symbolType != SCLASS) {
                    string base = string("Symbol ");
                    base += object->id + " is not a class";
                    fn(base.c_str(), lineno);
                    return NULL;
                }
                SymbolTable * classTable = classRow->table;
                TableRow * methodRow;
                // check for extension methods
                if (!isClass) {
                    methodRow = classTable->getMethodInfo(id);
                }
                else
                    methodRow = classTable->getSymbolInfo(SymbolTable::methodName(id, className));
                if (methodRow == NULL) {
                    string base = string("Method ");
                    base += id + " does not exist in class " + className;
                    fn(base.c_str(), lineno);
                    return NULL;
                }
                else {
                    MethodType * methodType = methodRow->methodInfo->methodType;
                    if (methodType->count != expList->count) {
                        fn("Method call arguments are incorrect", lineno);
                        return NULL;
                    }
                    else {
                        // check argument types
                        if (methodType->count != 0) {
                            for (int i = 0; i < methodType->count; i++) {
                                AST_Exp * exp = expList->exps[i];
                                ReturnType * expType = exp->typecheck(fn, isClass, mainClass, methodDecl);
                                if (!expType->equal(methodType->argTypes[i])) {
                                    string base = string("Method call argument at position ");
                                    base += i + " differs from definition";
                                    fn(base.c_str(), lineno);
                                    return NULL;
                                }
                            }
                        }
                        
                        return methodType->returnType;
                    }
                }
            }
        }
        case This: {
            // check if method exists in surrounding class
            SymbolTable * classTable = isClass ? mainClass->symbolTable : methodDecl->classTable;
            string className = isClass ? mainClass->id : methodDecl->parentClass->id;
            TableRow * methodRow = classTable->getSymbolInfo(SymbolTable::methodName(id, className));
            if (methodRow == NULL) {
                string base = string("Method ");
                base += id + " does not exist in class " + className;
                fn(base.c_str(), lineno);
                return NULL;
            }
            else {
                MethodType * methodType = methodRow->methodInfo->methodType;
                if (methodType->count != expList->count) {
                    fn("Method call arguments are incorrect", lineno);
                    return NULL;
                }
                else {
                    // check argument types
                    for (int i = 0; i < methodType->count; i++) {
                        AST_Exp * exp = expList->exps[i];
                        ReturnType * expType = exp->typecheck(fn, isClass, mainClass, methodDecl);
                        if (!expType->equal(methodType->argTypes[i])) {
                            string base = string("Method call argument at position ");
                            base += i + " differs from definition";
                            fn(base.c_str(), lineno);
                            return NULL;
                        }
                    }
                    return methodType->returnType;
                }
            }
            break;
        }
        case NewPrimeType: {
            fn("Cannot call method from primitive type", lineno);
            return NULL;
        }
    }
    return NULL;
}
ReturnType * Exp_Length::typecheck(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl) {
    // id . length
    // id must be an array, returns the size of the array
    TableRow * row;
    if (!isClass) {
        // check if symbol is in method first
        row = methodDecl->symbolTable->getSymbolInfo(id);
        if (row == NULL) {
            // check if symbol is in class or extended class
            row = methodDecl->parentClass->symbolTable->getSymbolInfo(id);
        }
    }
    else //main class
        row = mainClass->symbolTable->getSymbolInfo(id);
    if (row == NULL) {
        string base = string("Symbol ");
        base += id + " does not exist";
        fn(base.c_str(), lineno);
        return NULL;
    }
    if (row->symbolType != SVAR && row->symbolType != SARG) {
        string base = string("Symbol ");
        base += id + " is not a variable";
        fn(base.c_str(), lineno);
        return NULL;
    }
    if (!row->returnType->isArray) {
        string base = string("Symbol ");
        base += id + " is not an array";
        fn(base.c_str(), lineno);
        return NULL;
    }
    return new ReturnType(PINT);
}
ReturnType * Exp_IndexLength::typecheck(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl) {
    //int[][] i = new int[9][9];
    //System.out.println(i[0].length);
    // get symbol info
    TableRow * symbolInfo;
    if (isClass)
        symbolInfo = mainClass->symbolTable->getSymbolInfo(id);
    else {
        // check if local var first
        symbolInfo = methodDecl->symbolTable->getSymbolInfo(id);
        if (symbolInfo == NULL) {
            // check if in class
            symbolInfo = methodDecl->parentClass->symbolTable->getSymbolInfo(id);
        }
    }
    if (symbolInfo == NULL) {
        string base = string("Symbol ");
        base += id + " does not exist";
        fn(base.c_str(), lineno);
        return NULL;
    }
    // check that symbol is an array
    if (symbolInfo->symbolType != SVAR && symbolInfo->symbolType != SARG) {
        string base = string("Symbol ");
        base += id + " is not a variable";
        fn(base.c_str(), lineno);
        return NULL;
    }
    if (!symbolInfo->returnType->isArray) {
        string base = string("Symbol ");
        base += id + " is not an array";
        fn(base.c_str(), lineno);
        return NULL;
    }
    // check that index is an integer
    ReturnType * indexType = index->typecheck(fn, isClass, mainClass, methodDecl);
    if (indexType == NULL || indexType->type != PINT) {
        string base = string("Index expression for ");
        base += id + " is invalid";
        fn(base.c_str(), lineno);
        return NULL;
    }
    if (index->depth != symbolInfo->returnType->arrayDepth - 1) {
        cout << "Index depth: " << index->depth << ", symbol depth: " << symbolInfo->returnType->arrayDepth-1 << endl;
        string base = string("Index is invalid depth for ");
        base += id;
        fn(base.c_str(), lineno);
        return NULL;
    }
    return new ReturnType(PINT);
}

// Main typechecking calls
ReturnType * AST_Exp::typecheck(void (*fn)(const char * err, int lineno), AST_MainClass * mainClass) {
    return typecheck(fn, true, mainClass, NULL);
}
ReturnType * AST_Exp::typecheck(void (*fn)(const char * err, int lineno), AST_MethodDecl * methodDecl) {
   return typecheck(fn, false, NULL, methodDecl);
}
ReturnType * AST_Exp::typecheck(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl) {
    if (resolvedType)
        return type;
    switch(expression) {
        case Binary: {
            type = binaryOp->typecheck(fn, isClass, mainClass, methodDecl);
            break;
        }
        case Unary: {
            type = unaryOp->typecheck(fn, isClass, mainClass, methodDecl);
            break;
        }
        case Index: {
            type = index->typecheck(fn, isClass, mainClass, methodDecl);
            break;
        }
        case Length: {
            type = length->typecheck(fn, isClass, mainClass, methodDecl);
            break;
        }
        case Parens: {
            type = parens->exp->typecheck(fn, isClass, mainClass, methodDecl);
            break;
        }
        case IndexLength: {
            type = indexLength->typecheck(fn, isClass, mainClass, methodDecl);
            break;
        }
        case INT_LITERAL: {
            type = new ReturnType(PINT, 0);
            break;
        }
        case EBool: {
            type = new ReturnType(PBOOL, 0);
            break;
        }
        case Object: {
            type = object->typecheck(fn, isClass, mainClass, methodDecl);
            break;
        }
        case ObjectCall: {
            type = objectCall->typecheck(fn, isClass, mainClass, methodDecl);
            break;
        }
    }
    resolvedType = true;
    return type;
}