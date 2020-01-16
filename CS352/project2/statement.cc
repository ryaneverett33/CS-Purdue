#include "ast.hh"
#include "symboltable.hh"

ReturnValue * AST_Statement::interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke) {
    switch (type) {
        case StatementType::List:
            return statementList->interpret(isMethod, mainClass, methodInvoke);
        case StatementType::Print:
            return printStatement->interpret(isMethod, mainClass, methodInvoke);
        case StatementType::SBool:
            return boolStatement->interpret(isMethod, mainClass, methodInvoke);
        case StatementType::Assign:
            return assignStatement->interpret(isMethod, mainClass, methodInvoke);
        case StatementType::Return:
            return returnStatement->interpret(isMethod, mainClass, methodInvoke);
        case StatementType::Empty:
            return NULL;
    }
    return NULL;
}
void AST_Statement::typecheck(void (*fn)(const char * err, int lineno), AST_MainClass * mainClass) {
    typecheck(fn, true, mainClass, NULL);
}
void AST_Statement::typecheck(void (*fn)(const char * err, int lineno), AST_MethodDecl * methodDecl) {
    typecheck(fn, false, NULL, methodDecl);
}
void AST_Statement::typecheck(void (*fn)(const char * err, int lineno), bool isClass, AST_MainClass * mainClass, AST_MethodDecl * methodDecl) {
    switch (type) {
        case Empty:
            break;
        case Assign: {
            // check for proper symbols
            //TableRow * symbolInfo = methodDecl->symbolTable->getSymbolInfo(assignStatement->id);
            TableRow * symbolInfo;
            if (isClass) {
                // VarDecls don't exist in the main class
                string base = string("Symbol ");
                base += assignStatement->id + " doesn't exist";
                fn(base.c_str(), lineno);
                return;
            }
            else {
                symbolInfo = methodDecl->symbolTable->getSymbolInfo(assignStatement->id);
                if (symbolInfo == NULL) {
                    // check symbol exists in the class table
                    symbolInfo = methodDecl->parentClass->symbolTable->getSymbolInfo(assignStatement->id);
                    if (symbolInfo == NULL) {
                        // symbol doesn't exist 
                        string base = string("Symbol ");
                        base += assignStatement->id + " doesn't exist";
                        fn(base.c_str(), lineno);
                        return;
                    }
                }
            }
            if (symbolInfo->symbolType != SVAR && symbolInfo->symbolType != SARG) {
                // symbol is non-assignable error
                string base = string("Symbol ");
                base += assignStatement->id + " is not assignable";
                fn(base.c_str(), lineno);
            }
            else {
                ReturnType * rtype = assignStatement->exp->typecheck(fn, methodDecl);
                if (rtype == NULL)
                    return;
                if (assignStatement->idIndex) {
                    // arr[0] = 1;
                    // check index is an array matching the same size as symbol
                    // check index return type same size as symbol)
                    ReturnType * indexType = assignStatement->index->typecheck(fn, isClass, mainClass, methodDecl);
                    if (indexType->arrayDepth != symbolInfo->returnType->arrayDepth) {
                        string base = string("Array length mismatch, ");
                        base += assignStatement->id;
                        fn(base.c_str(), lineno);
                    }
                    if (rtype->type != symbolInfo->returnType->type) {
                        string base = string("Symbol assignment type mismatch, ");
                        base += assignStatement->id;
                        fn(base.c_str(), lineno);
                    }
                }
                else {
                    //arr = 1; arr = new int[5]; 
                    // check whether the types are the same
                    if (!rtype->equal(symbolInfo->returnType)) {
                        string base = string("Symbol type mismatch, ");
                        base += assignStatement->id;
                        fn(base.c_str(), lineno);
                    }
                }
            }
            break; 
        }
        case List: {
            for (vector<AST_Statement*>::iterator statement = statementList->statements.begin(); statement != statementList->statements.end(); statement++) {
                (*statement)->typecheck(fn, isClass, mainClass, methodDecl);
            }
            break;
        } 
        case SBool: {
            // if/while statements, check expressions
            //PType ptype = boolStatement->exp->resolveType(fn, false, NULL, methodDecl);
            ReturnType * rtype = boolStatement->exp->typecheck(fn, isClass, mainClass, methodDecl);
            if (rtype== NULL)
                return;
            if (rtype->type != PBOOL) {
                fn("Boolean statement requires a boolean type", lineno);
            }
            boolStatement->statement->typecheck(fn, isClass, mainClass, methodDecl);
            if (boolStatement->ifStatement)
                boolStatement->elseStatement->typecheck(fn, isClass, mainClass, methodDecl);
            break;
        }
        case Print: {
            // check exp if has one
            if (printStatement->printExp) {
                // only allow integers to print
                //PType ptype = printStatement->exp->resolveType(fn, false, NULL, methodDecl);
                ReturnType * rtype = printStatement->exp->typecheck(fn, isClass, mainClass, methodDecl);
                if (rtype == NULL)
                    return;
                if (rtype->type != PINT) {
                    fn("Print statement does not have an integer type", lineno);
                }
            }
            break;
        }
        case Return: {
            ReturnType * rtype = returnStatement->exp->typecheck(fn, isClass, mainClass, methodDecl);
            if (rtype == NULL)
                return;
            if (isClass) {
                // this literally is impossible
                fn("Can't return in a Main Class", lineno);
            }
            // int a() { return 1; }
            // 1 should match a's return type
            MethodType * type = methodDecl->getMethodType();
            if (!rtype->equal(type->returnType)) {
                fn("Return expression type does not match method definition", lineno);
            }
            break;
        }
    }
}
ReturnValue * StatementList::interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke) {
    for (vector<AST_Statement*>::iterator statement = statements.begin(); statement != statements.end(); statement++) {
        ReturnValue * value = (*statement)->interpret(isMethod, mainClass, methodInvoke);
        if (value != NULL)
            return value;
    }
    return NULL;
}
ReturnValue * Statement_Print::interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke) {
    if (printExp) {
        //cout << "Unable to print expression" << endl;
        ReturnValue * returnValue = exp->interpret(isMethod, mainClass, methodInvoke);
        if (returnValue == NULL)
            cout << "NULL";
        else
            cout << returnValue->intValue;
        if (println)
            cout << endl;
    }
    else {
        cout << stringLiteral;
        if (println)
            cout << endl;
    }
    return NULL;
}
ReturnValue * Statement_Boolean::interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke) {
    if (ifStatement) {
        //if statement
        ReturnValue * value = exp->interpret(isMethod, mainClass, methodInvoke);
        if (value->boolValue) {
            return statement->interpret(isMethod, mainClass, methodInvoke);
        }
        else {
            return elseStatement->interpret(isMethod, mainClass, methodInvoke);
        }
    }
    else {
        //while() do
        ReturnValue * value = exp->interpret(isMethod, mainClass, methodInvoke);
        while (value->boolValue) {
            ReturnValue * interpreted = statement->interpret(isMethod, mainClass, methodInvoke);
            if (interpreted != NULL)
                return interpreted;
            value = exp->interpret(isMethod, mainClass, methodInvoke);
        }
    }
    return NULL;
}
ReturnValue * Statement_Assign::interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke) {
    if (!isMethod) {
        cout << "Assignment statment within main function, not valid" << endl;
        return NULL;
    }
    // id = Exp
    // id Index = Exp
    ReturnValue * expValue = exp->interpret(isMethod, mainClass, methodInvoke);
    // get symbol info
    SymbolTable * symbolLocation;

    TableRow * symbolInfo = methodInvoke->methodTable->getSymbolInfo(id);
    symbolLocation = methodInvoke->methodTable;
    if (symbolInfo == NULL) {
        symbolInfo = methodInvoke->classTable->getSymbolInfo(id);
        symbolLocation = methodInvoke->classTable;
    }
    if (symbolInfo == NULL) {
        cout << "Failed to get symbol for " << id << endl;
        return NULL;
    }

    if (idIndex) {
        // array of where to assign
        ReturnValue * indexValue = index->interpret(isMethod, mainClass, methodInvoke);
        ReturnValue * toEdit;
            if (symbolInfo->symbolType == SVAR)
                toEdit = symbolInfo->varInfo->returnValue;
            else
                toEdit = symbolInfo->argInfo->returnValue;
            // fill info
            if (indexValue->arrayDepth == 1) {
                if (toEdit->returnType->type == PINT || toEdit->returnType->type == PBOOL)
                    toEdit->arr1[indexValue->arr1[0]] = (int)(toEdit->returnType->type == PINT ? expValue->intValue : expValue->boolValue);
                else
                    toEdit->objArr1[indexValue->arr1[0]] = expValue;
            }
            else {
                if (toEdit->returnType->type == PINT || toEdit->returnType->type == PBOOL)
                    toEdit->arr2[indexValue->arr1[0]][indexValue->arr1[1]] = (int)(toEdit->returnType->type == PINT ? expValue->intValue : expValue->boolValue);
                else
                    toEdit->objArr1[indexValue->arr1[0]][indexValue->arr1[1]] = expValue;
            }

            //reinsert back into symbol table
            if (symbolInfo->symbolType == SVAR) {
                symbolInfo->varInfo->returnValue = toEdit;
                symbolLocation->updateSymbolInfo(id, symbolInfo->varInfo);
            }
            else {
                symbolInfo->argInfo->returnValue = toEdit;
                symbolLocation->updateSymbolInfo(id, symbolInfo->argInfo);
            }
    }
    else {
        if (expValue->isArray) {
            ReturnValue * toEdit;
            if (symbolInfo->symbolType == SVAR)
                toEdit = symbolInfo->varInfo->returnValue;
            else
                toEdit = symbolInfo->argInfo->returnValue;
            // fill info 
            toEdit->objectValue = expValue->objectValue;
            toEdit->isArray = expValue->isArray;
            toEdit->arr1 = expValue->arr1;
            toEdit->arr2 = expValue->arr2;
            toEdit->arrayDepth = expValue->arrayDepth;
            toEdit->arraySize[0] = expValue->arraySize[0];
            toEdit->arraySize[1] = expValue->arraySize[1];

            //reinsert back into symbol table
            if (symbolInfo->symbolType == SVAR) {
                symbolInfo->varInfo->returnValue = toEdit;
                symbolLocation->updateSymbolInfo(id, symbolInfo->varInfo);
            }
            else {
                symbolInfo->argInfo->returnValue = toEdit;
                symbolLocation->updateSymbolInfo(id, symbolInfo->argInfo);
            }
        }
        else if (expValue->isObject) {
            ReturnValue * toEdit;
            if (symbolInfo->symbolType == SVAR)
                toEdit = symbolInfo->varInfo->returnValue;
            else
                toEdit = symbolInfo->argInfo->returnValue;

            // fill info 
            toEdit->objectValue = expValue->objectValue;
            toEdit->isObject = expValue->isObject;
            toEdit->initialized = expValue->initialized;
            toEdit->classTable = expValue->classTable;

            //reinsert back into symbol table
            if (symbolInfo->symbolType == SVAR) {
                symbolInfo->varInfo->returnValue = toEdit;
                symbolLocation->updateSymbolInfo(id, symbolInfo->varInfo);
            }
            else {
                symbolInfo->argInfo->returnValue = toEdit;
                symbolLocation->updateSymbolInfo(id, symbolInfo->argInfo);
            }
        }
        else if (expValue->isObjectArray) {
            ReturnValue * toEdit;
            if (symbolInfo->symbolType == SVAR)
                toEdit = symbolInfo->varInfo->returnValue;
            else
                toEdit = symbolInfo->argInfo->returnValue;
            // fill info 
            toEdit->objectValue = expValue->objectValue;
            toEdit->isObjectArray = expValue->isObjectArray;
            toEdit->objArr1 = expValue->objArr1;
            toEdit->objArr1 = expValue->objArr1;
            toEdit->arrayDepth = expValue->arrayDepth;
            toEdit->arraySize[0] = expValue->arraySize[0];
            toEdit->arraySize[1] = expValue->arraySize[1];

            //reinsert back into symbol table
            if (symbolInfo->symbolType == SVAR) {
                symbolInfo->varInfo->returnValue = toEdit;
                symbolLocation->updateSymbolInfo(id, symbolInfo->varInfo);
            }
            else {
                symbolInfo->argInfo->returnValue = toEdit;
                symbolLocation->updateSymbolInfo(id, symbolInfo->argInfo);
            }
        }
        else {
            //primitive value
            ReturnValue * toEdit;
            if (symbolInfo->symbolType == SVAR)
                toEdit = symbolInfo->varInfo->returnValue;
            else
                toEdit = symbolInfo->argInfo->returnValue;

            // fill info 
            if (expValue->returnType->type == PINT)
                toEdit->intValue = expValue->intValue;
            else if (expValue->returnType->type == PBOOL)
                toEdit->boolValue = expValue->boolValue;
            else {
                cout << "Primitive object that isn't an object" << endl;
                toEdit->objectValue = expValue->objectValue;
            }


            //reinsert back into symbol table
            if (symbolInfo->symbolType == SVAR) {
                symbolInfo->varInfo->returnValue = toEdit;
                symbolLocation->updateSymbolInfo(id, symbolInfo->varInfo);
            }
            else {
                symbolInfo->argInfo->returnValue = toEdit;
                symbolLocation->updateSymbolInfo(id, symbolInfo->argInfo);
            }
        }
        /*switch (expValue->returnType->type) {
            case PINT:
                // set value of arg/var
                if (symbolInfo->symbolType == SVAR) {
                    symbolInfo->varInfo->returnValue->intValue = expValue->intValue;
                    symbolLocation->updateSymbolInfo(id, symbolInfo->varInfo);
                }
                else {
                    // argument
                    symbolInfo->argInfo->returnValue->intValue = expValue->intValue;
                    symbolLocation->updateSymbolInfo(id, symbolInfo->argInfo);
                }
                break;
            case PBOOL:
                // set value of arg/var
                if (symbolInfo->symbolType == SVAR) {
                    symbolInfo->varInfo->returnValue->boolValue = expValue->boolValue;
                    symbolLocation->updateSymbolInfo(id, symbolInfo->varInfo);
                }
                else {
                    // argument
                    symbolInfo->argInfo->returnValue->boolValue = expValue->boolValue;
                    symbolLocation->updateSymbolInfo(id, symbolInfo->argInfo);
                }
                break;
            case POBJECT: {
                // set value of arg/var
                if (symbolInfo->symbolType == SVAR) {
                    // check if object or array
                    if (expValue->isArray) {
                        symbolInfo->varInfo->returnValue->objectValue = expValue->objectValue;
                        symbolInfo->varInfo->returnValue->isArray = expValue->isArray;
                        symbolInfo->varInfo->returnValue->arr1 = expValue->arr1;
                        symbolInfo->varInfo->returnValue->arr2 = expValue->arr2;
                        symbolInfo->varInfo->returnValue->arrayDepth = expValue->arrayDepth;
                        symbolInfo->varInfo->returnValue->arraySize[0] = expValue->arraySize[0];
                        symbolInfo->varInfo->returnValue->arraySize[1] = expValue->arraySize[1];
                    }
                    else {
                        // is object
                        symbolInfo->varInfo->returnValue->objectValue = expValue->objectValue;
                        symbolInfo->varInfo->returnValue->isObject = expValue->isObject;
                        symbolInfo->varInfo->returnValue->initialized = expValue->initialized;
                        symbolInfo->varInfo->returnValue->classTable = expValue->classTable;
                    }
                    symbolLocation->updateSymbolInfo(id, symbolInfo->varInfo);
                }
                else {
                    // check if object or array
                    if (expValue->isArray) {
                        symbolInfo->argInfo->returnValue->objectValue = expValue->objectValue;
                        symbolInfo->argInfo->returnValue->isArray = expValue->isArray;
                        symbolInfo->argInfo->returnValue->arr1 = expValue->arr1;
                        symbolInfo->argInfo->returnValue->arr2 = expValue->arr2;
                        symbolInfo->argInfo->returnValue->arrayDepth = expValue->arrayDepth;
                        symbolInfo->argInfo->returnValue->arraySize[0] = expValue->arraySize[0];
                        symbolInfo->argInfo->returnValue->arraySize[1] = expValue->arraySize[1];
                    }
                    else {
                        // is object
                        symbolInfo->argInfo->returnValue->objectValue = expValue->objectValue;
                        symbolInfo->argInfo->returnValue->isObject = expValue->isObject;
                        symbolInfo->argInfo->returnValue->initialized = expValue->initialized;
                        symbolInfo->argInfo->returnValue->classTable = expValue->classTable;
                    }
                    symbolLocation->updateSymbolInfo(id, symbolInfo->argInfo);
                }
                break;
            }
        }*/
    }
    return NULL;
}
ReturnValue * Statement_Return::interpret(bool isMethod, AST_MainClass * mainClass, MethodInvoke * methodInvoke) {
    // return Exp
    return exp->interpret(isMethod, mainClass, methodInvoke);
}