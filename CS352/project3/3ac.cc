#include "compile.hh"

//v1 <- new Obj, v1 <- new int
AddressCode * SetNew(Method method, string sadd1, AddressType add1, string sadd2, AddressType add2) {
    AddressCode * code = new AddressCode();
    code->type = CSETNEW;
    code->strAddress[0] = sadd1;
    code->strAddress[1] = sadd2;
    code->types[0] = add1;
    code->types[1] = add2;
    code->addressCount = 2;
    return code;
}
// y <- pop x, v1 <- pop x, 
/*AddressCode * SetPop(Method method, string sadd1, AddressType add1, string sadd2, AddressType add2) {
    AddressCode * code = new AddressCode();
    code->type = CSETPOP;
    code->addressCount = 2;
    code->strAddress[0] = sadd1;
    code->strAddress[1] = sadd2;
    code->types[0] = add1;
    code->types[1] = add2;
    return code;
}*/
// v1 = 1, v1 = a, v1 = !true
AddressCode * Set(Method method, string sadd1, int iadd1, AddressType add1,
string sadd2, int iadd2, AddressType add2, string rawOp) {
    return Set(method, sadd1, iadd1, add1, sadd2, iadd2, add2, sadd2, iadd2, err, rawOp);
}
// v1 = 1 + 1, v1 = true == false
AddressCode * Set(Method method, string sadd1, int iadd1, AddressType add1,
string sadd2, int iadd2, AddressType add2,
string sadd3, int iadd3, AddressType add3, string rawOp) {
    AddressOp op = parseOp(rawOp);
    AddressCode * code = new AddressCode();
    code->addressCount = add3 == err ? 2 : 3;
    code->type = CSET;
    code->op = op;
    // assign addresses
    code->types[0] = add1;
    code->types[1] = add2;
    if (add1 == IntLiteral || add1 == BoolLiteral)
        code->intAddress[0] = iadd1;
    else
        code->strAddress[0] = sadd1;
    if (add2 == IntLiteral || add2 == BoolLiteral)
        code->intAddress[1] = iadd2;
    else
        code->strAddress[1] = sadd2;

    if (code->addressCount == 2) {
        // i = 1, i = a, i = true, i = -1, i = !true
        if (op == Add)
            code->op = none;        // ignore i <- +1
    }
    else {
        // i = 1 op 1
        code->types[2] = add3;
        if (add3 == IntLiteral || add2 == BoolLiteral)
            code->intAddress[2] = iadd3;
        else
            code->strAddress[2] = sadd3;
    }
    return code;
}

AddressCode * SetNew(Method method, string sadd1, string sadd2, AddressType add1, AddressType add2) {
    AddressCode * code = new AddressCode();
    code->type = CSETNEW;
    code->types[0] = add1;
    code->types[1] = add2;
    code->strAddress[0] = sadd1;
    code->strAddress[1] = sadd2;
    code->addressCount = 2;
    return code;
}

// arr <- ARR 2 2, arr <- ARR 1
AddressCode * Arr(Method method, string sadd1, 
string sadd2, int iadd2, AddressType add2, string sadd3, int iadd3, AddressType add3,
bool is2d) {
    AddressCode * code = new AddressCode();
    code->type = CARR;
    code->addressCount = is2d ? 3 : 2;
    code->types[0] = SymReg;
    code->types[1] = add2;
    code->strAddress[0] = sadd1;
    if (add2 == IntLiteral) 
        code->intAddress[1] = iadd2;
    else
        code->strAddress[1] = sadd2;
    if (code->addressCount == 3) {
        code->types[2] = add3;
        if (add3 == IntLiteral)
            code->intAddress[2] = iadd3;
        else
            code->strAddress[2] = sadd3;
    }
    return code;
}

// v1 <- STORE -1
AddressCode * Store(Method method, string sadd1, AddressType add1, 
int iadd2, string sadd2, AddressType add2) {
    AddressCode * code = new AddressCode();
    code->type = CSTORE;
    code->types[0] = add1;
    code->types[1] = add2;
    code->strAddress[0] = sadd1;
    code->addressCount = 2;
    if (add2 == IntLiteral || add2 == BoolLiteral)
        code->intAddress[1] = iadd2;
    else
        code->strAddress[1] = sadd2;
    return code;
}

// goto loop_end
AddressCode * GoBack() {
    AddressCode * code = new AddressCode();
    code->type = CGOBACK;
    code->addressCount = 0;
    return code;
}
AddressCode * Mark() {
    AddressCode * code = new AddressCode();
    code->type = CMARK;
    code->addressCount = 0;
    return code;
}

// if a == b goto c where c is a function label (c can only be a function label)
AddressCode * BranchIf(string sadd1, int iadd1, AddressType add1,
string sadd2, int iadd2, AddressType add2, string label, string rawOp) {
    AddressOp op = parseOp(rawOp);
    AddressCode * code = new AddressCode();
    code->type = CIF;
    code->op = op;
    code->addressCount = 3;
    code->types[0] = add1;
    code->types[1] = add2;
    code->types[2] = FuncLabel;
    code->strAddress[2] = label;
    if (add1 == IntLiteral || add1 == BoolLiteral)
        code->intAddress[0] = iadd1;
    else
        code->strAddress[0] = sadd1;
    if (add2 == IntLiteral || add2 == BoolLiteral)
        code->intAddress[1] = iadd2;
    else
        code->strAddress[1] = sadd2;
    return code;
}

AddressCode * BranchElse(string label) {
    AddressCode * code = new AddressCode();
    code->type = CELSE;
    code->types[0] = FuncLabel;
    code->addressCount = 1;
    code->strAddress[0] = label;
    return code;
}

// CSPRINTLN "hello world"
AddressCode * PrintS(string message, bool println) {
    AddressCode * code = new AddressCode();
    code->type = println ? CSPRINTLN : CSPRINT;
    code->strAddress[0] = message;
    code->addressCount = 1;
    code->types[0] = PrintMessage;
    return code;
}

// CPRINTLN v1
AddressCode * PrintE(string sadd1, int iadd1, AddressType add1, bool println) {
    AddressCode * code = new AddressCode();
    code->type = println ? CPRINTLN : CPRINT;
    code->types[0] = add1;
    code->addressCount = 1;
    if (add1 == IntLiteral)
        code->intAddress[0] = iadd1;
    else
        code->strAddress[0] = sadd1;
    return code;
}

// push 1, pusAddressCode * Push(string sadd1, int iadd1, AddressType add1)h v1, push true
AddressCode * Push(string sadd1, int iadd1, AddressType add1) {
    AddressCode * code = new AddressCode();
    code->type = CPUSH;
    code->types[0] = add1;
    code->addressCount = 1;
    if (add1 == IntLiteral || add1 == BoolLiteral)
        code->intAddress[0] = iadd1;
    else
        code->strAddress[0] = sadd1;
    return code;
}

//return 1, return 2, return v1
AddressCode * ReturnV(string sadd1, int iadd1, AddressType add1) {
    AddressCode * code = new AddressCode();
    code->type = CRETURN;
    code->types[0] = add1;
    code->addressCount = 1;
    if (add1 == IntLiteral || add1 == BoolLiteral)
        code->intAddress[0] = iadd1;
    else
        code->strAddress[0] = sadd1;
    return code;
}

// v2 <- v1 call index
AddressCode * Call(string sadd1, AddressType add1, string sadd2, AddressType add2, 
string sadd3, AddressType add3) {
    AddressCode * code = new AddressCode();
    code->type = CCALL;
    code->addressCount = 3;
    code->strAddress[0] = sadd1;
    code->strAddress[1] = sadd2;
    code->strAddress[2] = sadd3;
    code->types[0] = add1;
    code->types[1] = add2;
    code->types[2] = add3;
    return code;
}

//v1 <- GET
AddressCode * Get(string sadd1, AddressType add1) {
    AddressCode * code = new AddressCode();
    code->type = CGET;
    code->addressCount = 1;
    code->types[0] = add1;
    code->strAddress[0] = sadd1;
    return code;
}

// v1 <- LENGTH v1
AddressCode * LengthV(string sadd1, AddressType add1) {
    AddressCode * code = new AddressCode();
    code->type = CLENGTH;
    code->addressCount = 1;
    code->types[0] = add1;
    code->strAddress[0] = sadd1;
    return code;
}

string AddressCode::str() {
    switch (type) {
        case CSET: {
            string base = strAddress[0] + " <- ";
            if (addressCount == 2) {
                if (op != none)
                    base += OpToStr(op);
                base += isInt(1) ? IntToString(1) : strAddress[1];
            }
            else {
                base += isInt(1) ? IntToString(1) : strAddress[1];
                base += OpToStr(op);
                base += isInt(2) ? IntToString(2) : strAddress[2];
            }
            return base;
        }
        case CSETNEW: {
            string base = strAddress[0] + " <- NEW " + strAddress[1];
            return base;
        }
        /*case CSETPOP: {
            string base = strAddress[0] + " <- POP " + strAddress[1];
            return base;
        }*/
        case CGOBACK: {
            return string("GOBACK");
        }
        case CMARK: {
            return string("MARK");
        }
        case CIF: {
            string base = string("IF ");
            base += (isInt(0) ? IntToString(0) : strAddress[0]) + " ";
            base += OpToStr(op) + " ";
            base += (isInt(1) ? IntToString(1) : strAddress[1]);
            base += " GOTO " + (isInt(2) ? IntToString(2) : strAddress[2]);
            return base;
        }
        case CELSE: {
            string base = "ELSE GOTO " + strAddress[0];
            return base;
        }
        case CSPRINTLN:
        case CSPRINT:  {
            string base = (type == CSPRINT) ? string("CSPRINT ") : string("CSPRINTLN ");
            base += strAddress[0];
            return base;
        }
        case CPRINTLN:
        case CPRINT: {
            string base = (type == CSPRINT) ? string("CPRINT ") : string("CPRINTLN ");
            if (types[0] == IntLiteral)
                base += IntToString(0);
            else
                base += strAddress[0];
            return base;
        }
        case CPUSH: {
            string base = string("PUSH ") + (isInt(0) ? IntToString(0) : strAddress[0]);
            return base;
        }
        case CCALL: {
            string base = strAddress[0] + " <- ";
            base += strAddress[1] + " CALL " + strAddress[2];
            return base;
        }
        case CRETURN: {
            string base = string("RETURN ") + (isInt(0) ? IntToString(0) : strAddress[0]);
            return base;
        }
        case CARR: {
            string base = strAddress[0] + " <- ARR ";
            if (types[1] == IntLiteral)
                base += IntToString(1) + " ";
            else
                base += strAddress[1] + " ";
            if (addressCount == 3) {
                if (types[2] == IntLiteral)
                    base += IntToString(2) + " ";
                else
                    base += strAddress[2] + " ";
            }
            return base;
        }
        case CSTORE: {
            string base = strAddress[0] + " <- STORE ";
            base += (isInt(1) ? IntToString(1) : strAddress[1]);
            return base;
        }
        case CGET: {
            string base = strAddress[0] + " <- GET";
            return base;
        }
        case CLENGTH: {
            string base = strAddress[0] + " <- LENGTH";
            return base;
        }
        default:
            return string(" ");
    }
}
AddressOp parseOp(string op) {
    if (op.compare("none") == 0)
        return none;
    else if (op.compare("+") == 0)
        return Add;
    else if (op.compare("-") == 0)
        return Sub;
    else if (op.compare("/") == 0)
        return Div;
    else if (op.compare("*") == 0)
        return Mul;
    else if (op.compare("==") == 0)
        return Equal;
    else if (op.compare(">") == 0)
        return GreaterThan;
    else if (op.compare(">=") == 0)
        return GreaterThanEqual;
    else if (op.compare("<") == 0)
        return LessThan;
    else if (op.compare("<=") == 0)
        return LessThanEqual;
    else if (op.compare("&&") == 0)
        return And;
    else if (op.compare("||") == 0)
        return Or;
    else if (op.compare("!") == 0)
        return Not;
    else
        return none;
}
string OpToStr(AddressOp op) {
    switch(op) {
        case Add:
            return string("+");
        case Sub:
            return string("-");
        case Div:
            return string("/");
        case Mul:
            return string("*");
        case Equal:
            return string("==");
        case GreaterThan:
            return string(">");
        case GreaterThanEqual:
            return string(">=");
        case LessThan:
            return string("<");
        case LessThanEqual:
            return string("<=");
        case And:
            return string("&&");
        case Or:
            return string("||");
        case Not:
            return string("!");
        default:
            return string(" ");
    }
}
string AddressCode::IntToString(int i) {
    if (types[i] == IntLiteral)
        return to_string(intAddress[i]);
    else
        return intAddress[i] == 1 ? string("true") : string("false");
}
bool AddressCode::isInt(int i) {
    return (types[i] == IntLiteral || types[i] == BoolLiteral) ? true : false;
}
// Creates the method name given a class::method
string Method::createMethodName(string className, string methodName) {
    // if className in methodName then return methodName
    if (methodName.find(className) != string::npos) {
        // methodName contains className
        return methodName;
    }
    return className + "_" + methodName;
}
// gets the method name given a class:(class_method)
string Method::fixMethodName(string className, string methodName) {
    if (methodName.find(className) != string::npos) {
        return methodName.substr(className.length() + 1);
    }
    return methodName;
}

// Creates a new branch method to be branched to
Method * Method::createBranch() {
    // create name
    string name = Method::createMethodName(this->className, this->name);
    name = name + "_b" + to_string(branchMethods.size());
    Method * branchMethod = new Method(name, this);
    branchMethod->targetNumber = branchMethods.size();
    addBranch(branchMethod);
    return branchMethod;
}
// Increase the result symbolic register in the last instruction added
// Returns the new symbolic register
string Method::increaseLastInstruction() {
    if (instructions.size() != 0) {
        int last = instructions.size() - 1;
        AddressCode * code = instructions[last];
        if (code->type == CSET) {
            if (code->types[0] == SymReg) {
                string symreg = code->strAddress[0];
                int value = symreg[1] - '0';       //convert ascii to decimal
                value++;
                symreg[1] = value + '0';
                code->strAddress[0] = symreg;
                instructions[last] = code;
                return code->strAddress[0];
            }
            else {
                cout << "unable to increase last instruction, result is not a symbolic register" << endl;
            }
        }
        else {
            cout << "unable to increase last instruction, TAC is not of type CSET" << endl;
        }
    }
    return string("");
}