#include "compile.hh"
#include <iostream>
#include <fstream>

std::ostream& operator<<(std::ostream& out, BinaryCase value){
    switch(value) {
        case IntBasic:
            return out << "IntBasic";
        case IntNest:
            return out << "IntNest";
        case IntTwoNest:
            return out << "IntTwoNest";
        case IntDoubleNested:
            return out << "IntDoubleNested";
        case IntExp:
            return out << "IntExp";
        case ExpBasic:
            return out << "ExpBasic";
        case ExpNest:
            return out << "ExpNest";
        case ExpTwoNest:
            return out << "ExpTwoNest";
        case ExpDoubleNested:
            return out << "ExpDoubleNested";
        default:
            return out << "UNKNOWN";
    }
}

// converts a program to it's IL representation
ILTable * Converter::convert(Program * program) {
    ILTable * table = new ILTable();
    table->program = program;
    Method  * main = new Method("main", &table->globalCounter);
    main->className = program->MainClass->id;
    convertStatement(main, program->MainClass->statement);
    table->addMethod(main->name, main);
    // iterate through each class
    for (vector<AST_ClassDecl*>::iterator classDecl = program->classDeclList->classDecls.begin();
    classDecl != program->classDeclList->classDecls.end(); classDecl++) {
        //cout << "Class (" << (*classDecl)->id << ") size: " << (*classDecl)->getSize() << endl;
        // iterate through each method in the class
        for (vector<AST_MethodDecl*>::iterator methodDecl = (*classDecl)->methodDeclList->methodDecls.begin();
        methodDecl != (*classDecl)->methodDeclList->methodDecls.end(); methodDecl++) {
            // convert each method
            string methodName = Method::createMethodName((*classDecl)->id, (*methodDecl)->id);
            //cout << "Function label for " << (*classDecl)->id << "::" << (*methodDecl)->id << ": " << methodName << endl;
            Method * method = new Method(methodName, &table->globalCounter);
            method->className = (*classDecl)->id;
            method->methodDecl = (*methodDecl);
            // convert statements
            for (vector<AST_Statement*>::iterator stmt = (*methodDecl)->statementList->statements.begin();
            stmt != (*methodDecl)->statementList->statements.end(); stmt++) {
                convertStatement(method, (*stmt));
            }
            convertReturnExpression(method, (*methodDecl)->returnExp);
            table->addMethod(methodName, method);

        }
    }
    return table;
}
void Converter::convertStatement(Method * method, AST_Statement * statement) {
    switch(statement->type) {
        case List: {
            for (vector<AST_Statement*>::iterator stmt = statement->statementList->statements.begin();
            stmt != statement->statementList->statements.end(); stmt++) {
                convertStatement(method, (*stmt));
            }
            break;
        }
        case SBool: {
            Statement_Boolean * stmt = statement->boolStatement;
            if (stmt->ifStatement) {
                Method * trueBranch = method->createBranch();
                Method * falseBranch = method->createBranch();
                // convert true-statement (create new branch)
                convertStatement(trueBranch, stmt->statement);
                // convert false-statement
                convertStatement(falseBranch, stmt->elseStatement);
                // convert exp
                AddressCode * code;
                if (stmt->exp->expression == EBool) {
                    string empty;
                    code = BranchIf(empty, stmt->exp->intLiteral, IntLiteral,
                        empty, 1, IntLiteral,
                        trueBranch->name, string("=="));
                }
                else {
                    string * expResult = convertExpression(method, stmt->exp, false);
                    code = BranchIf(*expResult, 0, SymReg, 
                        string(""), 1, IntLiteral,
                        trueBranch->name, string("=="));
                }
                method->addInstruction(code);
                code = BranchElse(falseBranch->name);
                method->addInstruction(code);
            }
            else {
                // while loop
                Method * loopBranch = method->createBranch();
                // convert statement to branch
                convertStatement(loopBranch, stmt->statement);
                // Goback from loop body
                AddressCode * code = GoBack();
                loopBranch->addInstruction(code);
                // mark return address BEFORE comparison
                code = Mark();
                method->addInstruction(code);
                // convert exp
                if (stmt->exp->expression == EBool) {
                    cout << "WARNING Infinite while loop detected on lineno: " << stmt->exp->lineno << endl;
                    string empty;
                    code = BranchIf(empty, stmt->exp->intLiteral, IntLiteral,
                        empty, 1, IntLiteral,
                        loopBranch->name, string("=="));
                }
                else {
                    string * expResult = convertExpression(method, stmt->exp, false);
                    code = BranchIf(*expResult, 0, SymReg, 
                        string(""), 1, IntLiteral,
                        loopBranch->name, string("=="));
                }
                method->addInstruction(code);
            }
            break;
        }
        case Print: {
            Statement_Print * stmt = statement->printStatement;
            AST_Exp * exp = stmt->exp;
            if (stmt->printExp) {
                if (exp->expression == INT_LITERAL) {
                    method->addInstruction(PrintE(string(), exp->intLiteral, IntLiteral, stmt->println));
                }
                else {
                    string * result = convertExpression(method, exp, false);
                    method->addInstruction(PrintE(*result, 0, SymReg, stmt->println));
                }
            }
            else {
                //print message
                //*(method->globalCount) = *(method->globalCount) + 1;
                string name = method->addGlobal(new Global("mprint", stmt->stringLiteral, *(method->globalCount), stmt->println));
                method->addInstruction(PrintS(name, stmt->println));
            }
            break;
        }
        case Assign: {
            Statement_Assign * stmt = statement->assignStatement;
            AST_Exp * exp = stmt->exp;
            string empty;
            if (stmt->idIndex) {
                AST_Exp ** indexArr = stmt->index->flatten();
                bool isInt[2] = {false, false};
                int ival[2] = {0,0};
                string * sval[2] = {new string(), new string()};
                for (int i = 0; i < stmt->index->depth; i++) {
                    AST_Exp * current = indexArr[i];
                    if (current->expression == INT_LITERAL) {
                        isInt[i] = true;
                        ival[i] = current->intLiteral;
                    }
                    else {
                        isInt[i] = false;
                        sval[i] = convertExpression(method, current, true);
                        if (i > 0 && !isInt[i-1]) {
                            string last = method->increaseLastInstruction();
                            sval[i] = &last;
                        }
                    }
                }
                // get array
                AddressCode * code = Set(*method, string("v1"), 0, SymReg,
                    stmt->id, 0, Variable, empty);
                method->addInstruction(code);
                // position array to index
                AddressType type1 = isInt[0] ? IntLiteral : SymReg;
                AddressType type2 = stmt->index->depth == 1 ? err : isInt[1] ? IntLiteral : SymReg;
                AddressCode * Arrcode = Arr(*method, string("v1"), *sval[0], ival[0], type1, *sval[1], ival[1], type2,
                    stmt->index->depth == 2 ? true : false);
                // store value in array
                if (exp->expression == INT_LITERAL) {
                    method->addInstruction(Arrcode);
                    code = Store(*method, string("v1"), SymReg, exp->intLiteral, empty, IntLiteral);
                    method->addInstruction(code);
                }
                else if (exp->expression == EBool) {
                    method->addInstruction(Arrcode);
                    code = Store(*method, string("v1"), SymReg, exp->intLiteral, empty, IntLiteral);
                    method->addInstruction(code);
                }
                else {
                    string * x = convertExpression(method, stmt->exp, true);
                    code = Store(*method, string("v1"), SymReg, 0, *x, SymReg);
                    method->addInstruction(Arrcode);
                    method->addInstruction(code);
                }
            }
            else {
                AddressCode * code;
                if (exp->expression == INT_LITERAL) {
                    code = Set(*method, stmt->id, 0, Variable, empty, exp->intLiteral, IntLiteral, " ");
                }
                else if (exp->expression == EBool) {
                    code = Set(*method, stmt->id, 0, Variable, empty, exp->intLiteral, IntLiteral, " ");
                }
                else {
                    string * x = convertExpression(method, stmt->exp, false);
                    code = Set(*method, stmt->id, 0, Variable, *x, 0, SymReg, " ");
                }
                method->addInstruction(code);
            }
            break;
        }
        case Return: {
            Statement_Return * stmt = statement->returnStatement;
            convertReturnExpression(method, stmt->exp);
            return;
        }
        case Empty:
            return;
    }
}
void Converter::convertReturnExpression(Method * method, AST_Exp * exp) {
    if (exp->expression == INT_LITERAL) {
        method->addInstruction(ReturnV(string(), exp->intLiteral, IntLiteral));
    }
    else if (exp->expression == EBool) {
        method->addInstruction(ReturnV(string(), exp->intLiteral, IntLiteral));
    }
    else {
        string * result = convertExpression(method, exp, false);
        method->addInstruction(ReturnV(*result, 0, SymReg));
    }
    return;
}
// returns the resulting symbolic register
string * Converter::convertExpression(Method * method, AST_Exp * expression, bool storeResult) {
    switch (expression->expression) {
        case Binary:
            return convertBinaryExpression(method, expression->binaryOp, storeResult);
        case Unary:
            return convertUnaryExpression(method, expression->unaryOp, storeResult);
        case Index:
            return convertIndexExpression(method, expression->index, storeResult);
        case Parens: {
            //cout << "parens" << endl;
            // if primitive type, resolve to symreg
            string empty;
            string * v2 = new string("v2");
            if (expression->parens->exp->expression == INT_LITERAL) {
                AddressCode * code = Set(*method, *v2, 0, SymReg,
                    empty, expression->parens->exp->intLiteral, IntLiteral, empty);
                method->addInstruction(code);
                return v2;
            }
            else if (expression->parens->exp->expression == EBool) {
                AddressCode * code = Set(*method, *v2, 0, SymReg,
                    empty, expression->parens->exp->intLiteral, IntLiteral, empty);
                method->addInstruction(code);
                return v2;
            }
            else {  // else convert interior expression
                return convertExpression(method, expression->parens->exp, true);
            }
        }
        case Length:
            return convertLengthExpression(method, expression->length, storeResult);
        case IndexLength:
            return convertIndexLengthExpression(method, expression->indexLength, storeResult);
        case Object:
            return convertObjectExpression(method, expression->object, storeResult);
        case ObjectCall:
            return convertObjectCallExpression(method, expression->objectCall, storeResult);
        default:
            return NULL;
    }
}
string * Converter::convertBinaryExpression(Method * method, Exp_BinaryOp * exp, bool storeResult) {
    int subcase = 0;
    BinaryCase classify = classifyBinary(exp, &subcase);
    //cout << "BinaryCase: " << classify << ", subcase: " << subcase << endl;
    string * v1 = !storeResult ? new string("v1") : new string("v2");
    string * v2 = !storeResult ? new string("v2") : new string("v3");
    string * v3 = !storeResult ? new string("v3") : new string("v4");
    string empty;
    switch (classify) {
        case IntBasic: {
            AddressCode * code = Set(*method, *v1, 0, SymReg, 
                empty, exp->left->intLiteral, IntLiteral, 
                empty, exp->right->intLiteral, IntLiteral, exp->op);
            method->addInstruction(code);
            return v1;
        }
        case IntNest: {
            if (subcase == 1) {
                // convert left first
                Exp_BinaryOp * leftOp = exp->left->parens->exp->binaryOp;
                // check if left nest is double nested
                int subsubcase = 0;
                BinaryCase sublassify = classifyBinary(leftOp, &subsubcase);
                if (sublassify == IntBasic) {
                    AddressCode * code = Set(*method, *v1, 0, SymReg,
                        empty, leftOp->left->intLiteral, IntLiteral,
                        empty, leftOp->right->intLiteral, IntLiteral, leftOp->op);
                    method->addInstruction(code);
                    // do op with right included
                    code = Set(*method, *v1, 0, SymReg,
                        *v1, 0, SymReg, empty, exp->right->intLiteral, IntLiteral, exp->op);
                    method->addInstruction(code);
                    return v1;
                }
                else {
                    cout << "ugly nest in intnest" << endl;
                    // evalute left side
                    string * x = convertBinaryExpression(method, leftOp, false);
                    // do op with right included
                    AddressCode * code = Set(*method, *x, 0, SymReg,
                        *x, 0, SymReg, empty, exp->right->intLiteral, IntLiteral, exp->op);
                    method->addInstruction(code);
                    return x;
                }
            }
            else {
                // convert right first
                Exp_BinaryOp * rightOp = exp->right->parens->exp->binaryOp;
                // check if left nest is double nested
                int subsubcase = 0;
                BinaryCase subclassify = classifyBinary(rightOp, &subsubcase);
                if (subclassify == IntBasic) {
                    AddressCode * code = Set(*method, *v1, 0, SymReg,
                        empty, rightOp->left->intLiteral, IntLiteral,
                        empty, rightOp->right->intLiteral, IntLiteral, rightOp->op);
                    method->addInstruction(code);
                    // do op with left included
                    code = Set(*method, *v1, 0, SymReg, 
                        empty, exp->left->intLiteral, IntLiteral,
                        *v1, 0, SymReg, exp->op);
                    method->addInstruction(code);
                    return v1;
                }
                else {
                    cout << "ugly nest in intnest" << endl;
                    // evalute right side
                    string * x = convertBinaryExpression(method, rightOp, false);
                    // do op with right included
                    AddressCode * code = Set(*method, *x, 0, SymReg, 
                        empty, exp->left->intLiteral, IntLiteral,
                        *x, 0, SymReg, exp->op);
                    method->addInstruction(code);
                    return x;
                }
                
            }
        }
        case IntTwoNest: {
            Exp_BinaryOp * leftOp = exp->left->parens->exp->binaryOp;
            Exp_BinaryOp * rightOp = exp->right->parens->exp->binaryOp;
            // convert left
            AddressCode * code = Set(*method, *v1, 0, SymReg,
                empty, leftOp->left->intLiteral, IntLiteral,
                empty, leftOp->right->intLiteral, IntLiteral, leftOp->op);
            method->addInstruction(code);
            // convert right
            code = Set(*method, *v2, 0, SymReg,
                empty, rightOp->left->intLiteral, IntLiteral,
                empty, rightOp->right->intLiteral, IntLiteral, rightOp->op);
            method->addInstruction(code);
            // op left and right
            code = Set(*method, *v1, 0, SymReg,
                *v1, 0, SymReg, *v2, 0, SymReg, exp->op);
            method->addInstruction(code);
            return v1;
        }
        case IntDoubleNested: {
            Exp_BinaryOp * leftOp = exp->left->parens->exp->binaryOp;
            Exp_BinaryOp * rightOp = exp->right->parens->exp->binaryOp;
            if (subcase == 1) {
                Exp_BinaryOp * llNestOp = leftOp->left->parens->exp->binaryOp;
                Exp_BinaryOp * lrNestOp = leftOp->right->parens->exp->binaryOp;
                Exp_BinaryOp * rlNestOp = rightOp->left->parens->exp->binaryOp;
                Exp_BinaryOp * rrNestOp = rightOp->right->parens->exp->binaryOp;
                // v1 <- op ll
                AddressCode * code = Set(*method, *v1, 0, SymReg,
                    empty, llNestOp->left->intLiteral, IntLiteral,
                    empty, llNestOp->right->intLiteral, IntLiteral, llNestOp->op);
                method->addInstruction(code);
                // v2 <- op lr
                code = Set(*method, *v2, 0, SymReg,
                    empty, lrNestOp->left->intLiteral, IntLiteral,
                    empty, lrNestOp->right->intLiteral, IntLiteral, lrNestOp->op);
                method->addInstruction(code);
                // v3 <- v1 op v2
                code = Set(*method, *v3, 0, SymReg,
                    *v1, 0, SymReg, *v2, 0, SymReg, leftOp->op);
                method->addInstruction(code);
                // v1 <- op rl
                code = Set(*method, *v1, 0, SymReg,
                    empty, rlNestOp->left->intLiteral, IntLiteral,
                    empty, rlNestOp->right->intLiteral, IntLiteral, rlNestOp->op);
                method->addInstruction(code);
                // v2 <- op rr
                code = Set(*method, *v2, 0, SymReg,
                    empty, rrNestOp->left->intLiteral, IntLiteral,
                    empty, rrNestOp->right->intLiteral, IntLiteral, rrNestOp->op);
                method->addInstruction(code);
                // v1 <- v1 op v2
                code = Set(*method, *v1, 0, SymReg,
                    *v1, 0, SymReg, *v2, 0, SymReg, rightOp->op);
                method->addInstruction(code);
                // v1 <- v3 op v1
                code = Set(*method, *v1, 0, SymReg,
                    *v3, 0, SymReg, *v1, 0, SymReg, exp->op);
                method->addInstruction(code);
                return v1;
            }
            else if (subcase == 2) {
                Exp_BinaryOp * llNestOp = leftOp->left->parens->exp->binaryOp;
                Exp_BinaryOp * lrNestOp = leftOp->right->parens->exp->binaryOp;
                // v1 <- op ll
                AddressCode * code = Set(*method, *v1, 0, SymReg,
                    empty, llNestOp->left->intLiteral, IntLiteral,
                    empty, llNestOp->right->intLiteral, IntLiteral, llNestOp->op);
                method->addInstruction(code);
                // v2 <- op lr
                code = Set(*method, *v2, 0, SymReg,
                    empty, lrNestOp->left->intLiteral, IntLiteral,
                    empty, lrNestOp->right->intLiteral, IntLiteral, lrNestOp->op);
                method->addInstruction(code);
                // v3 <- v1 op v3
                code = Set(*method, *v3, 0, SymReg,
                    *v1, 0, SymReg, *v2, 0, SymReg, leftOp->op);
                method->addInstruction(code);
                // v1 <- op rightOp
                code = Set(*method, *v1, 0, SymReg,
                    empty, rightOp->left->intLiteral, IntLiteral,
                    empty, rightOp->right->intLiteral, IntLiteral, rightOp->op);
                method->addInstruction(code);
                // v1 <- v3 op v1
                code = Set(*method, *v1, 0, SymReg,
                    *v3, 0, SymReg, *v1, 0, SymReg, exp->op);
                method->addInstruction(code);
                return v1;
            }
            else if (subcase == 3) {
                Exp_BinaryOp * rlNestOp = rightOp->left->parens->exp->binaryOp;
                Exp_BinaryOp * rrNestOp = rightOp->right->parens->exp->binaryOp;
                // v1 <- op rl
                AddressCode * code = Set(*method, *v1, 0, SymReg,
                    empty, rlNestOp->left->intLiteral, IntLiteral,
                    empty, rlNestOp->right->intLiteral, IntLiteral, rlNestOp->op);
                method->addInstruction(code);
                // v2 <- op rr
                code = Set(*method, *v1, 0, SymReg,
                    empty, rrNestOp->left->intLiteral, IntLiteral,
                    empty, rrNestOp->right->intLiteral, IntLiteral, rrNestOp->op);
                method->addInstruction(code);
                // v3 <- v1 op v2
                code = Set(*method, *v3, 0, SymReg,
                    *v1, 0, SymReg, *v2, 0, SymReg, leftOp->op);
                method->addInstruction(code);
                // v1 <- op leftOp
                code = Set(*method, *v1, 0, SymReg,
                    empty, leftOp->left->intLiteral, IntLiteral,
                    empty, leftOp->right->intLiteral, IntLiteral, leftOp->op);
                method->addInstruction(code);
                // v1 <- v1 op v3
                code = Set(*method, *v1, 0, SymReg,
                    *v3, 0, SymReg, *v1, 0, SymReg, exp->op);
                method->addInstruction(code);
                return v1;
            }
        }
        case IntExp: {
            if (subcase == 1) {
                // resolve right as x
                string * x = convertExpression(method, exp->right, false);
                // left op x
                AddressCode * code = Set(*method, *x, 0, SymReg,
                    empty, exp->left->intLiteral, IntLiteral,
                    *x, 0, SymReg, exp->op);
                method->addInstruction(code);
                return x;
            }
            else {
                // resolve left as x
                string * x = convertExpression(method, exp->left, false);
                // x op right
                AddressCode * code = Set(*method, *x, 0, SymReg,
                    *x, 0, SymReg,
                    empty, exp->right->intLiteral, IntLiteral, exp->op);
                method->addInstruction(code);
                return x;
            }
        }
        case ExpBasic: {
            // resolve left as x
            string * x = convertExpression(method, exp->left, false);
            // resolve right as y
            string * y = convertExpression(method, exp->right, true);
            // x op y
            AddressCode * code = Set(*method, *x, 0, SymReg,
                *x, 0, SymReg,
                *y, 0, SymReg, exp->op);
            method->addInstruction(code);
            return x;
        }
        case ExpNest: {
            if (subcase == 1) {
                // convert left first
                Exp_BinaryOp * leftOp = exp->left->parens->exp->binaryOp;
                // check if left nest is double nested
                int subsubcase = 0;
                BinaryCase sublassify = classifyBinary(leftOp, &subsubcase);
                if (sublassify == ExpBasic) {
                    string * x = convertExpression(method, leftOp->left, false);
                    string * y = convertExpression(method, leftOp->right, true);
                    // v2 <- (left op right)
                    AddressCode * code = Set(*method, *y, 0, SymReg,
                        *x, 0, SymReg,
                        *y, 0, SymReg, leftOp->op);
                    method->addInstruction(code);
                    // get right
                    string * z = convertExpression(method, exp->right, false);
                    // v2 op right
                    code = Set(*method, *v1, 0, SymReg,
                        *y, 0, SymReg,
                        *z, 0, SymReg, exp->op);
                    method->addInstruction(code);
                    return v1;
                }
                else {
                    string * x = convertExpression(method, exp->left, true);
                    // v1 <- get right
                    string * z = convertExpression(method, exp->right, false);
                    // left(v2) op right
                    AddressCode * code = Set(*method, *v1, 0, SymReg,
                        *x, 0, SymReg,
                        *z, 0, SymReg, exp->op);
                    method->addInstruction(code);
                    return v1;
                }
            }
            else {
                // convert right first
                Exp_BinaryOp * rightOp = exp->right->parens->exp->binaryOp;
                // check if right nest is double nested
                int subsubcase = 0;
                BinaryCase sublassify = classifyBinary(rightOp, &subsubcase);
                if (sublassify == ExpBasic) {
                    string * y = convertExpression(method, rightOp->left, false);
                    string * z = convertExpression(method, rightOp->right, true);
                    // v2 <- y op z
                    AddressCode * code = Set(*method, *z, 0, SymReg,
                        *y, 0, SymReg,
                        *z, 0, SymReg, rightOp->op);
                    method->addInstruction(code);
                    // get left
                    string * x = convertExpression(method, exp->left, false);
                    // left op v2
                    code = Set(*method, *v1, 0, SymReg,
                        *x, 0, SymReg,
                        *z, 0, SymReg, exp->op);
                    method->addInstruction(code);
                    return v1;
                }
                else {
                    string * y = convertExpression(method, exp->right, true);
                    // v1 <- get left
                    string * x = convertExpression(method, exp->left, false);
                    // left op right(v2)
                    AddressCode * code = Set(*method, *v1, 0, SymReg,
                        *x, 0, SymReg,
                        *y, 0, SymReg, exp->op);
                    method->addInstruction(code);
                    return v1;
                }
            }
        }
        case ExpTwoNest: {
            Exp_BinaryOp * leftOp = exp->left->parens->exp->binaryOp;
            Exp_BinaryOp * rightOp = exp->right->parens->exp->binaryOp;
            // get ll
            string * ll = convertExpression(method, leftOp->left, false);
            // get lr
            string * lr = convertExpression(method, leftOp->right, true);
            // v3 <- ll op lr
            AddressCode * code = Set(*method, *v3, 0, SymReg,
                *ll, 0, SymReg,
                *lr, 0, SymReg, leftOp->op);
            method->addInstruction(code);
            // get rl
            string * rl = convertExpression(method, rightOp->left, false);
            // get rr
            string * rr = convertExpression(method, rightOp->right, true);
            // v1 <- rl op rr
            code = Set(*method, *v1, 0, SymReg,
                *rl, 0, SymReg,
                *rr, 0, SymReg, rightOp->op);
            method->addInstruction(code);
            // v1 <- v3 op v1
            code = Set(*method, *v1, 0, SymReg,
                *v3, 0, SymReg,
                *v1, 0, SymReg, exp->op);
            method->addInstruction(code);
            return v1;
        }
        case ExpDoubleNested: {
            if (subcase == 1)
                return convertExpDoubleNestedCase1(method, exp, storeResult);
            else if (subcase == 2)
                return convertExpDoubleNestedCase2(method, exp, storeResult);
            else
                return convertExpDoubleNestedCase3(method, exp, storeResult);
        }
    }
    return v1;
}
string * Converter::convertUnaryExpression(Method * method, Exp_UnaryOp * exp, bool storeResult) {
    string * use = !storeResult ? new string("v1") : new string("v2");
    string empty;
    
    if (exp->exp->expression == INT_LITERAL) {
        if (exp->op == '-') {
            AddressCode * code = Set(*method, *use, 0, SymReg, empty, exp->exp->intLiteral, IntLiteral, string("-"));
            method->addInstruction(code);
            return use;
        }
        AddressCode * code = Set(*method, *use, 0, SymReg, empty, exp->exp->intLiteral, IntLiteral, string());
        method->addInstruction(code);
        return use;
    }
    else if (exp->exp->expression == EBool) {
        AddressCode * code = Set(*method, *use, 0, SymReg, empty, exp->exp->boolLiteral, IntLiteral, string("!"));
        method->addInstruction(code);
        return use;
    }
    else {
        string * newResult = convertExpression(method, exp->exp, false);
        // result <- op result
        string opString = "0";
        opString[0] = exp->op;
        AddressCode * code = Set(*method, *newResult, 0, SymReg, *newResult, 0, SymReg, opString);
        method->addInstruction(code);
        return newResult;
    }
}
string * Converter::convertIndexExpression(Method * method, Exp_Index * exp, bool storeResult) {
    string * v1 = !storeResult ? new string("v1") : new string("v2");
    // load variable
    AddressCode * code = Set(*method, *v1, 0, SymReg,
        exp->id, 0, Variable, " ");
    method->addInstruction(code);
    // ARR variable
    AST_Exp ** indexArr = exp->index->flatten();
    bool isInt[2] = {false, false};
    int ival[2] = {0,0};
    string * sval[2] = {new string(), new string()};
    for (int i = 0; i < exp->index->depth; i++) {
        AST_Exp * current = indexArr[i];
        if (current->expression == INT_LITERAL) {
            isInt[i] = true;
            ival[i] = current->intLiteral;
        }
        else {
            isInt[i] = false;
            sval[i] = convertExpression(method, current, true);
            if (i > 0 && !isInt[i-1]) {
                string last = method->increaseLastInstruction();
                sval[i] = &last;
            }
        }
    }
    AddressType type1 = isInt[0] ? IntLiteral : SymReg;
    AddressType type2 = exp->index->depth == 1 ? err : isInt[1] ? IntLiteral : SymReg;
    code = Arr(*method, *v1, *sval[0], ival[0], type1, *sval[1], ival[1], type2, exp->index->depth == 2);
    method->addInstruction(code);
    // GET variable
    code = Get(*v1, SymReg);
    method->addInstruction(code);
    return v1;
}
string * Converter::convertIndexLengthExpression(Method * method, Exp_IndexLength * exp, bool storeResult) {
    string * v1 = !storeResult ? new string("v1") : new string("v2");
    string empty;
    // is 2d array
    // get object
    AddressCode * code = Set(*method, *v1, 0, SymReg, exp->id, 0, Variable, empty);
    method->addInstruction(code);
    // set array indices
    code = Arr(*method, *v1, empty, -1, IntLiteral, empty, -1, IntLiteral, true);
    method->addInstruction(code);
    // do LENGTH
    code = LengthV(*v1, SymReg);
    method->addInstruction(code);
    return v1;
}
string * Converter::convertLengthExpression(Method * method, Exp_Length * exp, bool storeResult) {
    string * v1 = !storeResult ? new string("v1") : new string("v2");
    string empty;
    // is 1d array
    // get object
    AddressCode * code = Set(*method, *v1, 0, SymReg, exp->id, 0, Variable, empty);
    method->addInstruction(code);
    // set array indices
    code = Arr(*method, *v1, empty, -1, IntLiteral, empty, -1, IntLiteral, false);
    method->addInstruction(code);
    // do LENGTH
    code = LengthV(*v1, SymReg);
    method->addInstruction(code);
    return v1;
}
string * Converter::convertObjectExpression(Method * method, AST_Object * exp, bool storeResult) {
    string * v1 = !storeResult ? new string("v1") : new string("v2");
    string * v2 = !storeResult ? new string("v2") : new string("v3");
    string empty;
    switch (exp->type) {
        case OID: {
            // id
            AddressCode * code = Set(*method, *v1, 0, SymReg, exp->id, 0, Variable, empty);
            method->addInstruction(code);
            return v1;
        }
        case This: {
            string * thisstr = new string("THIS");
            AddressCode * code = Set(*method, *v1, 0, SymReg, *thisstr, 0, Obj, empty);
            method->addInstruction(code);
            return v1;
        }
        case NewID: {
            //new id ()
            AddressCode * code = SetNew(*method, *v1, exp->id, SymReg, Obj);
            method->addInstruction(code);
            return v1;
        }
        case NewPrimeType:
        default: {
            //new PrimeType Index
            // create object
            AST_PrimeType * primeType = exp->newPrimeType->primeType;
            AST_Index * index = exp->newPrimeType->index;
            AddressCode * code;
            switch (primeType->type) {
                case Int:
                    code = SetNew(*method, *v1, string("INT"), SymReg, PrimType);
                    break;
                case TBool:
                    code = SetNew(*method, *v1, string("BOOL"), SymReg, PrimType);
                    break;
                case TID:
                    code = SetNew(*method, *v1, primeType->IDValue, SymReg, PrimType);
                    break;
            }
            // make it an array
            AST_Exp ** indexArr = index->flatten();
            bool isInt[2] = {false, false};
            int ival[2] = {0,0};
            string * sval[2] = {new string(), new string()};
            for (int i = 0; i < index->depth; i++) {
                AST_Exp * current = indexArr[i];
                if (current->expression == INT_LITERAL) {
                    isInt[i] = true;
                    ival[i] = current->intLiteral;
                }
                else {
                    isInt[i] = false;
                    sval[i] = convertExpression(method, current, true);
                    if (i > 0 && !isInt[i-1]) {
                        string last = method->increaseLastInstruction();
                        sval[i] = &last;
                    }
                }
            }
            method->addInstruction(code);   //Create after resolving indices
            AddressType type1 = isInt[0] ? IntLiteral : SymReg;
            AddressType type2 = index->depth == 1 ? err : isInt[1] ? IntLiteral : SymReg;
            code = Arr(*method, *v1, *sval[0], ival[0], type1, *sval[1], ival[1], type2, index->depth == 2);
            method->addInstruction(code);
            return v1;
        }
    }
}
string * Converter::convertObjectCallExpression(Method * method, Exp_ObjectCall * exp, bool storeResult) {
    string * v1 = !storeResult ? new string("v1") : new string("v2");
    string * v2 = !storeResult ? new string("v2") : new string("v3");
    string empty;
    // resolve arguments
    for (vector<AST_Exp*>::iterator arg = exp->expList->exps.begin();
    arg != exp->expList->exps.end(); arg++) {
        if ((*arg)->expression == INT_LITERAL) {
            // push arg to stack
            AddressCode * code = Push(empty, (*arg)->intLiteral, IntLiteral);
            method->addInstruction(code);
        }   
        else if ((*arg)->expression == EBool) {
            // push arg to stack
            AddressCode * code = Push(empty, (*arg)->boolLiteral, BoolLiteral);
            method->addInstruction(code);
        }
        else {
            // resolve arg to symreg
            string * x = convertExpression(method, (*arg), true);
            AddressCode * code = Push(*x, 0, SymReg);
            method->addInstruction(code);
        }
    }
    // get object
    string * obj = convertObjectExpression(method, exp->object, false);
    AddressCode * code = Call(*v1, SymReg, *obj, SymReg, exp->id, FuncLabel);
    method->addInstruction(code);
    return v1;
}
// writes table to disk
void Converter::debugWriteOut(ILTable * table) {
    ofstream output;
    output.open("debug.il");
    output << "Globals" << endl;
    for (vector<Global*>::iterator global = table->globals.begin(); global != table->globals.end(); global++) {
        output << (*global)->name << "=" << (*global)->value << endl;
    }
    output << endl;
    for (vector<string>::iterator method = table->methods.begin(); method != table->methods.end(); method++) {
        output << (*method) << ":" << endl;
        Method * methodObj = table->table[(*method)];
        for (vector<AddressCode*>::iterator instruction = methodObj->instructions.begin(); 
        instruction != methodObj->instructions.end(); instruction++) {
            output << "\t" << (*instruction)->str() << endl;
        }
    }
    output.close();
}
// Classifies a binary expression and it's subcase
// e.g x+y -> ExpBasic, subcase=0 || x+1 -> IntExp, subcase=1
BinaryCase classifyBinary(Exp_BinaryOp * binary, int * subcase) {
    // check what expression contains
    bool leftContainsExp = false;
    bool leftNested = false;
    bool leftDoubleNested = false;
    bool rightContainsExp = false;
    bool rightNested = false;
    bool rightDoubleNested = false;

    // check what left contains
    if (binary->left->expression == INT_LITERAL || binary->left->expression == EBool)
        leftContainsExp = false;
    else if (binary->left->expression == Parens) {
        leftNested = true;
        // check if underlying is exp or ints
        Exp_Parens * parens = binary->left->parens;
        if (parens->exp->expression == Binary) {
            Exp_BinaryOp * leftNestedBinary = parens->exp->binaryOp;
            int nestedSubCase = 0;
            BinaryCase nestedCase = classifyBinary(leftNestedBinary, &nestedSubCase);
            // if nestedCase is IntBasic then left is single nested
            // if nestedCase is IntNest or IntTwoNest then left is double nested
            // if nestedCase is ExpNest or ExpTwoNest then left is double nested 
            // else IntExp -> evaluate to exp
            if (nestedCase == IntBasic)
                leftContainsExp = false;
            else if (nestedCase == IntNest || nestedCase == IntTwoNest) {
                leftContainsExp = false;
                leftDoubleNested = true;
            }
            else if (nestedCase == ExpNest || nestedCase == ExpTwoNest) {
                leftContainsExp = true;
                leftDoubleNested = true;
            }
            else
                leftContainsExp = true;
        }
        else
            leftContainsExp = true;
    }
    else    // else it's an exp
        leftContainsExp = true;

    // check what right contains
    if (binary->right->expression == INT_LITERAL || binary->right->expression == EBool)
        rightContainsExp = false;
    else if (binary->right->expression == Parens) {
        rightNested = true;
        // check if underlying is exp or ints
        Exp_Parens * parens = binary->right->parens;
        if (parens->exp->expression == Binary) {
            Exp_BinaryOp * rightNestedBinary = parens->exp->binaryOp;
            int nestedSubCase = 0;
            BinaryCase nestedCase = classifyBinary(rightNestedBinary, &nestedSubCase);
            // if nestedCase is IntBasic then right is single nested
            // if nestedCase is IntNest or IntTwoNest then right is double nested
            // if nestedCase is ExpNest or ExpTwoNest then right is double nested 
            // else IntExp -> evaluate to exp
            if (nestedCase == IntBasic)
                rightContainsExp = false;
            else if (nestedCase == IntNest || nestedCase == IntTwoNest) {
                rightContainsExp = false;
                rightDoubleNested = true;
            }
            else if (nestedCase == ExpNest || nestedCase == ExpTwoNest) {
                rightContainsExp = true;
                rightDoubleNested = true;
            }
            else
                rightContainsExp = true;
        }
        else
            rightContainsExp = true;
    }
    else    // else it's an exp
        rightContainsExp = true;

    // Perform classification
    if (!leftContainsExp && !rightContainsExp) {
        if (leftNested && !rightNested) {   // (1+1)+1
            *subcase = 1;
            return IntNest;
        }
        else if (!leftNested && rightNested) {  // 1+(1+1)
            *subcase = 2;
            return IntNest;
        }
        else if (leftDoubleNested || rightDoubleNested) {
            if (leftDoubleNested && rightDoubleNested) {    //((1+1)+(2+2))+((3+3)+(4+4))
                *subcase = 1;
                return IntDoubleNested;
            }
            else if (leftDoubleNested && !rightDoubleNested) { //((1+1)+(2+2))+(1+1)
                *subcase = 2;
                return IntDoubleNested;
            }
            else if (!leftDoubleNested && rightDoubleNested) { //(1+1)+((1+1)+(2+2))
                *subcase = 3;
                return IntDoubleNested;
            }
        }
        else if (leftNested && rightNested) {   // (1+1)+(1+1)
            *subcase = 0;
            return IntTwoNest;
        }
        else { // 1+1
            *subcase = 0;
            return IntBasic;
        }
    }
    else if (leftContainsExp && rightContainsExp) {
        if (leftNested && !rightNested) {   // (x+y)+x
            *subcase = 1;
            return ExpNest;
        }
        else if (!leftNested && rightNested) {  // x+(x+y)
            *subcase = 2;
            return ExpNest;
        }
        else if (leftDoubleNested || rightDoubleNested) {
            if (leftDoubleNested && rightDoubleNested) {    //((x+y)+(y+z))+((a+b)+(c+d))
                *subcase = 1;
                return ExpDoubleNested;
            }
            else if (leftDoubleNested && !rightDoubleNested) { //((x+y)+(y+z))+(a+b)
                *subcase = 2;
                return ExpDoubleNested;
            }
            else if (!leftDoubleNested && rightDoubleNested) { //(x+y)+((a+b)+(c+d))
                *subcase = 3;
                return ExpDoubleNested;
            }
        }
        else if (leftNested && rightNested) {   // (x+y)+(x+y)
            *subcase = 0;
            return ExpTwoNest;
        }
        else { // x+y
            *subcase = 0;
            return ExpBasic;
        }
    }
    else if (leftContainsExp && !rightContainsExp) {    //x+1
        if (rightNested) {
            // treat as x+y
            *subcase = 0;
            return ExpBasic;
        }
        else {
            *subcase = 2;
            return IntExp;
        }
    }
    else if (!leftContainsExp && rightContainsExp) {    //1+x
        if (leftNested) {
            // treat as y+x
            *subcase = 0;
            return ExpBasic;
        }
        else {
            *subcase = 1;
            return IntExp;
        }
    }
    return ExpBasic;
}
string * Converter::convertExpDoubleNestedCase1(Method * method, Exp_BinaryOp * exp, bool storeResult) {
    string * v1 = !storeResult ? new string("v1") : new string("v2");
    string * v2 = !storeResult ? new string("v2") : new string("v3");
    string * v3 = !storeResult ? new string("v3") : new string("v4");
    string * v4 = !storeResult ? new string("v4") : new string("v5");
    string empty;
    Exp_BinaryOp * left = exp->left->parens->exp->binaryOp;
    Exp_BinaryOp * right = exp->right->parens->exp->binaryOp;
    Exp_BinaryOp * ll = left->left->parens->exp->binaryOp;
    Exp_BinaryOp * lr = left->right->parens->exp->binaryOp;
    Exp_BinaryOp * rl = right->left->parens->exp->binaryOp;
    Exp_BinaryOp * rr = right->right->parens->exp->binaryOp;

    // convert left side
    string * x = convertExpression(method, ll->left, false);
    string * y = convertExpression(method, ll->right, true);
    AddressCode * code = Set(*method, *v3, 0, SymReg,
        *x, 0, SymReg,
        *y, 0, SymReg, ll->op);
    method->addInstruction(code);
    string * w = convertExpression(method, lr->left, false);
    string * z = convertExpression(method, lr->right, true);
    code = Set(*method, *v1, 0, SymReg,
        *w, 0, SymReg,
        *z, 0, SymReg, lr->op);
    method->addInstruction(code);
    code = Set(*method, *v4, 0, SymReg,
        *v3, 0, SymReg,
        *v1, 0, SymReg, left->op);
    method->addInstruction(code);

    // convert right side
    string * a = convertExpression(method, rl->left, false);
    string * b = convertExpression(method, rl->right, true);
    code = Set(*method, *v3, 0, SymReg,
        *a, 0, SymReg,
        *b, 0, SymReg, rl->op);
    method->addInstruction(code);
    string * c = convertExpression(method, rr->left, false);
    string * d = convertExpression(method, rr->right, true);
    code = Set(*method, *v1, 0, SymReg,
        *c, 0, SymReg,
        *d, 0, SymReg, rr->op);
    method->addInstruction(code);
    code = Set(*method, *v1, 0, SymReg,
        *v1, 0, SymReg,
        *v2, 0, SymReg, right->op);
    method->addInstruction(code);

    // left op right
    code = Set(*method, *v1, 0, SymReg,
        *v4, 0, SymReg,
        *v1, 0, SymReg, exp->op);
    method->addInstruction(code);
    return v1;
}
string * Converter::convertExpDoubleNestedCase2(Method * method, Exp_BinaryOp * exp, bool storeResult) {
    string * v1 = !storeResult ? new string("v1") : new string("v2");
    string * v2 = !storeResult ? new string("v2") : new string("v3");
    string * v3 = !storeResult ? new string("v3") : new string("v4");
    string * v4 = !storeResult ? new string("v4") : new string("v5");
    string empty;
    Exp_BinaryOp * left = exp->left->parens->exp->binaryOp;
    Exp_BinaryOp * right = exp->right->parens->exp->binaryOp;
    Exp_BinaryOp * ll = left->left->parens->exp->binaryOp;
    Exp_BinaryOp * lr = left->right->parens->exp->binaryOp;

    // convert left side
    string * x = convertExpression(method, ll->left, false);
    string * y = convertExpression(method, ll->right, true);
    AddressCode * code = Set(*method, *v3, 0, SymReg,
        *x, 0, SymReg,
        *y, 0, SymReg, ll->op);
    method->addInstruction(code);
    string * w = convertExpression(method, lr->left, false);
    string * z = convertExpression(method, lr->right, true);
    code = Set(*method, *v1, 0, SymReg,
        *w, 0, SymReg,
        *z, 0, SymReg, lr->op);
    method->addInstruction(code);
    code = Set(*method, *v4, 0, SymReg,
        *v3, 0, SymReg,
        *v1, 0, SymReg, left->op);
    method->addInstruction(code);

    // convert right side
    string * a = convertExpression(method, right->left, false);
    string * b = convertExpression(method, right->right, true);
    code = Set(*method, *v1, 0, SymReg,
        *v1, 0, SymReg,
        *v2, 0, SymReg, right->op);
    method->addInstruction(code);

    // left op right
    code = Set(*method, *v1, 0, SymReg,
        *v4, 0, SymReg,
        *v1, 0, SymReg, exp->op);
    method->addInstruction(code);
    return v1;
}
string * Converter::convertExpDoubleNestedCase3(Method * method, Exp_BinaryOp * exp, bool storeResult) {
    string * v1 = !storeResult ? new string("v1") : new string("v2");
    string * v2 = !storeResult ? new string("v2") : new string("v3");
    string * v3 = !storeResult ? new string("v3") : new string("v4");
    string * v4 = !storeResult ? new string("v4") : new string("v5");
    string empty;
    Exp_BinaryOp * left = exp->left->parens->exp->binaryOp;
    Exp_BinaryOp * right = exp->right->parens->exp->binaryOp;
    Exp_BinaryOp * rl = right->left->parens->exp->binaryOp;
    Exp_BinaryOp * rr = right->right->parens->exp->binaryOp;
    
    // convert right side
    string * x = convertExpression(method, rl->left, false);
    string * y = convertExpression(method, rl->right, true);
    AddressCode * code = Set(*method, *v3, 0, SymReg,
        *x, 0, SymReg,
        *y, 0, SymReg, rl->op);
    method->addInstruction(code);
    string * w = convertExpression(method, rr->left, false);
    string * z = convertExpression(method, rr->right, true);
    code = Set(*method, *v1, 0, SymReg,
        *w, 0, SymReg,
        *z, 0, SymReg, rr->op);
    method->addInstruction(code);
    code = Set(*method, *v4, 0, SymReg,
        *v1, 0, SymReg,
        *v2, 0, SymReg, right->op);
    method->addInstruction(code);

    // convert left side
    string * a = convertExpression(method, left->left, false);
    string * b = convertExpression(method, left->right, true);
    code = Set(*method, *v1, 0, SymReg,
        *v1, 0, SymReg,
        *v2, 0, SymReg, right->op);
    method->addInstruction(code);
    
    // left op right
    code = Set(*method, *v1, 0, SymReg,
        *v4, 0, SymReg,
        *v1, 0, SymReg, exp->op);
    method->addInstruction(code);
    return v1;
}