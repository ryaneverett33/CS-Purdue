#include "compile.hh"
#include <iostream>
#include <fstream>

void Compiler::compile(Program * program) {
    allocateRegisters(program);
    this->program = program;
    instructions = new vector<string>();
    init_constants();
    // add globals
    for (vector<Global*>::iterator global = table->globals.begin(); global != table->globals.end(); global++) {
        instructions->push_back((*global)->toInstruction());
    }
    init_alignment();
    compute_offsets();
    // convert methods
    for (int i = 0; i < table->methods.size(); i++) {
        useTab = true;
        string methodName = table->methods[i];
        Method * method = table->table[methodName];
        currentMethod = method;
        addMethod(method);
        if (method->isMain())
            saveLinkRegister();
        else
            init_method(method);
        for (currentInstructionCount = 0; currentInstructionCount < method->instructions.size();
        currentInstructionCount++) {
            AddressCode * code = method->instructions[currentInstructionCount];
            // convert TAC to ASM
            compileAddressCode(code, method);
        }
        if (method->isMain())
            restoreLinkRegister();
        else if (method->isChild)
            exit_method(method);
    }
    currentMethod = NULL;
    
    // write out
    writeout(program->name);
}
void Compiler::allocateRegisters(Program * program) {
    for (int i = 0; i < table->methods.size(); i++) {
        string methodName = table->methods[i];
        Method * method = table->table[methodName];
        for (vector<AddressCode*>::iterator instruction = method->instructions.begin();
        instruction != method->instructions.end(); instruction++) {
            AddressCode * code = (*instruction);
            // check if any types contain symbol register
            for (int j = 0; j < code->addressCount; j++) {
                if (code->types[j] == SymReg) {
                    basicAllocation(code, method->isMain());
                    break;
                }
            }
        }
    }
}
// lazily converts symbolic registers to actual registers
void Compiler::basicAllocation(AddressCode * code, bool isMainMethod) {
    for (int i = 0; i < code->addressCount; i++) {
        if (code->types[i] == SymReg) {
            // convert symreg to reg
            string symReg = code->strAddress[i];        // of form v1
            int number = symReg[1] - '0';       //convert ascii to decimal
            string newReg = "r" + to_string(number);
            code->strAddress[i] = newReg;
            code->types[i] = Reg;
        }
    }
}

void Compiler::writeout(string name) {
    ofstream output;
    output.open(name + ".s");
    for (int i = 0; i < instructions->size(); i++) {
        output << (*instructions)[i] << endl;
    }
    output.close();
}

// Creates the initial program layout
void Compiler::init_constants() {
    string layout[] = {
        ".section .text",
        "@ CONSTANTS",
        "println: .asciz \"%d\\n\"",
        "print: .asciz \"%d\"",
    };
    // sizeof(layout) / sizeof(layout[0]) returns the length of layout
    for (int i = 0; i < sizeof(layout) / sizeof(layout[0]); i++) {
        addInstruction(layout[i]);
    }
}
// Initializes a method 
void Compiler::init_method(Method * method) {
    string instruction;
    if (method->isChild) {
        // save lr
        instruction = string("PUSH {lr}");
        addInstruction(instruction);
    }
    else {
        // setup stack base
        instruction = string("MOV r9, sp");
        addInstruction(instruction);
        TableRow * classInfo = lookupClassInfo(method);
        TableRow * methodInfo = lookupMethodInfo(classInfo->table, method);
        int argcount = methodInfo->methodInfo->argCount;
        instruction = string("ADD r9, r9, #") + to_string(argcount * 4);
        addInstruction(instruction);
        // push LR
        instruction = string("PUSH {lr}");
        addInstruction(instruction);
        // setup variables
        AST_MethodDecl * methodDecl = methodInfo->node->astMethodDecl;
        if (methodDecl->varDeclList->count != 0) {
            int varOffset = (methodDecl->varDeclList->count * 4);
            instruction = string("SUB sp, sp, #") + to_string(varOffset);
            addInstruction(instruction);
        }
    }
}
// handles exiting a branching method
void Compiler::exit_method(Method * method) {
    string instruction = string("POP {pc}");
    addInstruction(instruction);
}
// computes stack offset for vars/args per class and method
void Compiler::compute_offsets() {
    SymbolTable * globalTable = program->symbolTable;
    for (int i = 0; i < globalTable->rows.size(); i++) {
        TableRow * globalRow = globalTable->rows[i];
        if (globalRow->table->inheritedTable != NULL) {
            globalRow->table = globalRow->table->resolveInheritedTable();
        }
        SymbolTable * classTable = globalRow->table;
        int classVarOffset = 0;
        for (int j = 0; j < classTable->rows.size(); j++) {
            TableRow * classRow = classTable->rows[j];
            AST_MethodDecl * methodDecl = classRow->node->astMethodDecl;
            if (classRow->symbolType == SVAR) {
                // calculate offset for row
                classRow->argInfo->offset = 4 * classVarOffset;
                classVarOffset++;
            }
            else if (classRow->symbolType == SMETHOD) {
                SymbolTable * methodTable = classRow->table;
                int methodVarOffset = 0;
                int methodArgOffset = methodDecl->varDeclList->varDecls.size();
                if (methodArgOffset != 0)
                    methodArgOffset--;
                for (int x = 0; x < methodTable->rows.size(); x++) {
                    TableRow * methodRow = methodTable->rows[x];
                    if (methodRow->symbolType == SVAR) {
                        methodRow->varInfo->offset = 4 * methodVarOffset;
                        methodVarOffset++;
                    }
                    if (methodRow->symbolType == SARG) {
                        // arguments are in backwards order
                        methodRow->argInfo->offset = 4 * methodArgOffset;
                        methodArgOffset--;
                    }
                }
            }
        }
    }
}
void Compiler::init_alignment() {
    addInstruction(".global main");
    addInstruction(".balign 4");
}
// adds the method to instructions
void Compiler::addMethod(Method * method) {
    instructions->push_back(method->name + ":");
    curlineno++;
}
// Converts TAC to ASM
void Compiler::compileAddressCode(AddressCode * code, Method * method) {
    switch(code->type) {
        case CSET:
            compileSet(code, method);
            break;
        case CSETNEW:
            compileSetNew(code, method);
            break;
        case CIF:
        case CELSE:
            compileIfElse(code, method, code->type == CIF);
            break;
        case CSPRINTLN:
        case CSPRINT:
        case CPRINTLN:
        case CPRINT:
            compilePrint(code, method);
            break;
        case CPUSH:
            compilePush(code, method);
            break;
        case CCALL:
        case CRETURN:
            compileCallReturn(code, method, code->type == CCALL);
            break;
        case CARR:
        case CLENGTH:
        case CSTORE:
        case CGET:
            compileArray(code, method);
            break;
        case CMARK:
        case CGOBACK:
            compileMarkGoBack(code, method, code->type == CMARK);
            break;
    }
    lastInstruction = code;
}
void Compiler::compilePrint(AddressCode * code, Method * method) {
    bool printLine = false;     // for exps
    switch (code->type) {
        case CSPRINTLN:
        case CSPRINT: {
            addInstruction(string("LDR r0, =") + code->strAddress[0]);
            pushLinkRegister();
            callStd(true);
            popLinkRegister();
            break;
        }
        case CPRINTLN:
            printLine = true;
        case CPRINT: {
            if (printLine)
                addInstruction("LDR r0, =println");
            else
                addInstruction("LDR r0, =print");
            if (code->types[0] == IntLiteral)
                addInstruction(string("MOV r1, #") + to_string(code->intAddress[0]));
            else if (code->types[0] == Reg) {
                // check if register is r1, else move to r1
                int reg = parseRegisterTarget(code->strAddress[0]);
                if (reg != 1) {
                    addInstruction(string("MOV r1, r") + to_string(reg));
                }
            }
            pushLinkRegister();
            callStd(true);
            popLinkRegister();
            break;
        }
    }
}
// ifOp: whether the operation is an if statement or else statement
void Compiler::compileIfElse(AddressCode * code, Method * method, bool ifOp) {
    string instruction;
    AddressCode * nextInstruction = NULL;
    int upper = 2;  // shitty hack for while loops
    bool isWhileLoop = false;
    if (peekNextInstruction()->type == CELSE) {
        nextInstruction = consumeNextInstruction();
    }
    else {
        upper--;
        isWhileLoop = true;
    }
    for (int i = 0; i< upper; i++) {
        if (code->types[0] == IntLiteral && code->types[1] == IntLiteral) {
            // 1 == 1
            // set r10 to value
            instruction = string("MOV r10, #") + to_string(code->intAddress[0]);
            addInstruction(instruction);
            // cmp values
            instruction = string("CMP r10, #") + to_string(code->intAddress[1]);
            addInstruction(instruction);
        }
        else {
            // v1 == 1
            // cmp register and immediate
            instruction = string("CMP ") + code->strAddress[0] + ", #";
            instruction += to_string(code->intAddress[1]);
            addInstruction(instruction);
        }
        // handle branching (function label in strAddress[2])
        if (i == 0) {
            instruction = string("BLEQ ") + code->strAddress[2];
            addInstruction(instruction);
            if (isWhileLoop)
                whileLine.push(curlineno);
        }
        else {
            // this will get ignored if it's a while loop
            // redo the comparison for nested branching
            instruction = string("BLNE ") + nextInstruction->strAddress[0];
            addInstruction(instruction);
        }
    }
}
// isCall: whether the operation is a call operation or a return operation
void Compiler::compileCallReturn(AddressCode * code, Method * method, bool isCall) {
    if (isCall) {   // of form v1 <- v1 call method
        string result = code->strAddress[0];
        // get classname
        int reg = parseRegisterTarget(result);
        string funclabel = Method::createMethodName(info.className, code->strAddress[2]);
        // push object
        string instruction = string("PUSH {") + code->strAddress[1] + "}";
        addInstruction(instruction);
        // save lr
        if (!method->isMain())
            pushStackBase();
        // bl function label
        instruction = string("BL ") + funclabel;
        addInstruction(instruction);
        if (!method->isMain())
            popStackBase();
        // mov from r0 to result
        instruction = string("MOV ") + result + ", r0";
        addInstruction(instruction);
    }
    else {
        string instruction;
        // move result to r1
        if (code->types[0] == IntLiteral) {
            instruction = string("MOV r0, #") + to_string(code->intAddress[0]);
            addInstruction(instruction);
        }
        else if (code->types[0] == Reg) {
            int regTarget = parseRegisterTarget(code->strAddress[1]);
            if (regTarget != 0) {
                // move to r0
                instruction = string("MOV r0, ") + code->strAddress[0];
                addInstruction(instruction);
            }
        }
        // set pc to lr
        // get lr from stack
        TableRow * classInfo = lookupClassInfo(method);
        if (classInfo == NULL)
            return;
        TableRow * methodInfo = lookupMethodInfo(classInfo->table, method);
        if (methodInfo == NULL)
            return;
        // link reg is [argcount x 4] + 4
        int offset = (methodInfo->methodInfo->argCount * 4) + 4;
        instruction = string("MOV r10, r9");
        addInstruction(instruction);
        instruction = string("SUB r10, #") + to_string(offset);
        addInstruction(instruction);
        addInstruction("MOV sp, r9");
        instruction = string("LDR pc, [r10]");
        addInstruction(instruction);
    }
}
// isMark: whether the operation is a mark operation or a goback operation
void Compiler::compileMarkGoBack(AddressCode * code, Method * method, bool isMark) {
    if (isMark) {
        markedLines.push(curlineno);
    }
    else {
        // subtract lr
        // pop the lr
        string instruction = string("POP {lr}");
        addInstruction(instruction);
        int markedLine = markedLines.front();
        markedLines.pop();
        int whileSaved = whileLine.front();
        whileLine.pop();
        int difference = whileSaved - markedLine;
        // subtract lr from it
        instruction = string("SUB lr, lr, #") + to_string(difference * 4);
        addInstruction(instruction);
        instruction = string("PUSH {lr}");
        addInstruction(instruction);
    }
}
// compile instructions for ARR, STORE, and GET
void Compiler::compileArray(AddressCode * code, Method * method) {
    if (code->type == CARR) {
        string result = code->strAddress[0];
        string instruction;
        AddressCode * nextInstruction = consumeNextInstruction();
        if (nextInstruction->type == CLENGTH) {
            if (code->addressCount == 2) {
                // 1d
                instruction = string("LDR ") + result + ", [" + result + "]";
                addInstruction(instruction);
            } 
            else {
                // 2d
                // copy to r10
                instruction = string("MOV r10, ") + result;
                addInstruction(instruction);
                // offset to get 2d length
                instruction = string("ADD r10, r10, #4");
                addInstruction(instruction);
                // get length
                instruction = string("LDR ") + result + ", [r10]";
                addInstruction(instruction);
            }
        }
        else if (nextInstruction->type == CSTORE) {
            // move array to scratch
            instruction = string("MOV r10, ") + result;
            addInstruction(instruction);
            if (code->addressCount == 2) {
                // 1d store
                // offset the array
                if (code->types[1] == IntLiteral) {
                    instruction = string("ADD r10, r10, #") + to_string((code->intAddress[1] * 4)+4);
                    addInstruction(instruction);
                }
                else { 
                    // multiply register by 4
                    // load 4 to address
                    instruction = string("MOV r6, #4");
                    addInstruction(instruction);
                    instruction = string("MUL ") + code->strAddress[1] + ", " + code->strAddress[1] + ", r6";
                    addInstruction(instruction);
                    instruction = string("ADD ") + code->strAddress[1] + ", #4";
                    addInstruction(instruction);
                    instruction = string("ADD r10, r10, ") + code->strAddress[1];
                    addInstruction(instruction);
                }
                // store in array
                if (nextInstruction->types[1] == IntLiteral) {
                    // copy immediate to scratch r6
                    instruction = string("MOV r6, #") + to_string(nextInstruction->intAddress[1]);
                    addInstruction(instruction);
                    instruction = string("STR r6, [r10]");
                    addInstruction(instruction);
                }
                else {
                    instruction = string("STR ") + nextInstruction->strAddress[1];
                    instruction += ", [r10]";
                    addInstruction(instruction);
                }
            }
            else {
                // 2d store
                if (code->types[1] == IntLiteral && code->types[2] == IntLiteral) {
                    // store immediate ix2 + j+4
                    int offset = (2*code->intAddress[1]) + code->intAddress[2];
                    offset += 4;
                    instruction = string("ADD r10, r10, #") + to_string(offset);
                    addInstruction(instruction);
                }
                else if (code->types[1] == Reg && code->types[2] == Reg) {
                    instruction = string("MOV r6, ") + code->strAddress[1];
                    addInstruction(instruction);
                    instruction = string("MOV r7, #2");
                    addInstruction(instruction);
                    instruction = string("MUL r6, r6, r7");
                    addInstruction(instruction);
                    instruction = string("ADD r6, r6, ") + code->strAddress[2];
                    addInstruction(instruction);
                    instruction = string("ADD r6, r6, #4");
                    addInstruction(instruction);
                }
                // store in array
                if (nextInstruction->types[1] == IntLiteral) {
                    // copy immediate to scratch r6
                    instruction = string("MOV r6, #") + to_string(nextInstruction->intAddress[1]);
                    addInstruction(instruction);
                    instruction = string("STR r6, [r10]");
                    addInstruction(instruction);
                }
                else {
                    instruction = string("STR ") + nextInstruction->strAddress[1];
                    instruction += ", [r10]";
                    addInstruction(instruction);
                }
            }
        }
        else if (nextInstruction->type == CGET) {
            // offset address
            if (code->addressCount == 2) {
                // 1d array
                if (code->types[1] == IntLiteral) {
                    instruction = string("ADD ") + result + ", #";
                    instruction += to_string((code->intAddress[1] *4)+4);
                    addInstruction(instruction);
                }
                else if (code->types[1] == Reg) {
                    // offset reg
                    instruction = string("MOV r6, #4");
                    addInstruction(instruction);
                    instruction = string("MUL ") + result + ", " + result + ", r6";
                    addInstruction(instruction);
                    instruction = string("ADD ") + result + ", " + result + ", #4";
                    addInstruction(instruction);
                }
            }
            else {
                if (code->types[1] == IntLiteral && code->types[2] == IntLiteral) {
                    int offset = (code->intAddress[1] * 2) + code->intAddress[2];
                    offset += 4;
                    instruction = string("ADD ") + result + ", #";
                    instruction += to_string(offset);
                    addInstruction(instruction);
                }
                else if (code->types[1] == Reg && code->types[2] == Reg) {
                    // offset = i*2 + j + 4
                    instruction = string("MOV r6, ") + code->strAddress[1];
                    addInstruction(instruction);
                    instruction = string("MOV r7, #2");
                    addInstruction(instruction);
                    instruction = string("MUL r6, r6, r7");
                    addInstruction(instruction);
                    instruction = string("ADD r6, r6, ") + code->strAddress[2];
                    addInstruction(instruction);
                    instruction = string("ADD r6, r6, #4");
                    addInstruction(instruction);
                }
            }
            // get value
            instruction = string("LDR ") + nextInstruction->strAddress[0] + ", [" + nextInstruction->strAddress[0] + "]";
            addInstruction(instruction);
        }
    }
}
void Compiler::compilePush(AddressCode * code, Method * method) {
    string instruction;
    if (code->types[0] == IntLiteral) {
        instruction = string("MOV r10, #") + to_string(code->intAddress[0]);
        addInstruction(instruction);
        instruction = string("PUSH {r10}");
    }
    else
        instruction = string("PUSH {") + code->strAddress[0] + "}";
    addInstruction(instruction);
}
void Compiler::compileSet(AddressCode * code, Method * method) {
    if (code->addressCount == 2) {
        // check if op is none
        // else unary op
        string result = code->strAddress[0];
        if (code->op == none) {
            if (code->types[0] == Reg && code->types[1] == Reg) {
                // simple move
                string instruction = string("MOV ") + result + ", " + code->strAddress[1];
                addInstruction(instruction);
            }
            else if (code->types[0] == Reg && code->types[1] == IntLiteral) {
                // set register to immediate
                string instruction = string("MOV ") + result + ", #" + to_string(code->intAddress[1]);
                addInstruction(instruction);
            }
            else if (code->types[0] == Variable && code->types[1] != Variable) {
                // store value
                // get variable info from symbol table
                TableRow * classRow = lookupClassInfo(method);
                if (classRow == NULL)
                    return;
                // check if class var or method arg/var
                bool isInClass = false;
                bool isInMethod = false;
                // get method info
                TableRow * methodRow = lookupMethodInfo(classRow->table, method);
                if (methodRow == NULL)
                    return;
                int argcount = methodRow->methodInfo->argCount;
                // look if class has symbol
                TableRow * info = classRow->table->getSymbolInfo(code->strAddress[0]);
                if (info == NULL) {
                    isInMethod = true;
                    // look in method for symbol
                    info = methodRow->table->getSymbolInfo(code->strAddress[0]);
                    if (info == NULL) {
                        cout << "Failed Symbol Table lookup for " << code->strAddress[0] << " in compileSet" << endl;
                        return;
                    }
                }
                else
                    isInClass = true;
                // get offset in stack (object stack versus local stack)
                int absOffset = 0;
                if (isInClass)
                    absOffset = info->varInfo->offset;
                else {
                    if (info->symbolType == SARG)
                        absOffset = info->argInfo->offset;
                    else {
                        // absoffset = [# of args * 4] + 4 + 4 + reloffset
                        int relOffset = absOffset;
                        absOffset = (argcount * 4);
                        if (absOffset == 0)
                            absOffset += 4;
                        absOffset += 4;
                        absOffset += relOffset;
                    }
                }
                // load stack info to register
                if (isInClass) {
                    // calculate offset to the object in the stack
                    int objectOffset = argcount == 0 ? 0 : argcount * 4;
                    string instruction = string("MOV r10, r9");
                    addInstruction(instruction);
                    instruction = string("SUB r10, r10, #") + to_string(objectOffset);
                    addInstruction(instruction);    //r10 points to object address
                    instruction = string("LDR r10, [r10]");
                    addInstruction(instruction);
                }
                else {
                    string instruction = string("MOV r10, r9");
                    addInstruction(instruction);    //r10 points to stack
                }
                // offset register
                string instruction;
                if (isInClass)  // malloc is ADD
                    instruction = string("ADD r10, r10, #") + to_string(absOffset);
                else            // stack is sub
                    instruction = string("SUB r10, r10, #") + to_string(absOffset);
                addInstruction(instruction);
                if (code->types[1] == Reg) {
                    // STORE register in register
                    instruction = string("STR ") + code->strAddress[1] + ", [r10]";
                    addInstruction(instruction);
                }
                else {
                    // IntLiteral
                    instruction = string("MOV r8, #") + to_string(code->intAddress[1]);
                    addInstruction(instruction);
                    // STORE register in register
                    instruction = string("STR r8, [r10]");
                    addInstruction(instruction);
                }
            }
            else if (code->types[0] == Reg && code->types[1] == Obj) {
                // v1 <- THIS
                // get this from stack
                TableRow * classRow = lookupClassInfo(method);
                if (classRow == NULL)
                    return;
                TableRow * methodRow = lookupMethodInfo(classRow->table, method);
                if (methodRow == NULL)
                    return;
                int stackOffset = methodRow->methodInfo->argCount * 4;
                // mov stack base to result
                string instruction = string("MOV ") + result + ", r9";
                addInstruction(instruction);
                // subtract offset from stack base to get Object pointer
                instruction = string("SUB ") + result + ", #" + to_string(stackOffset);
                addInstruction(instruction);
            }
            else {
                // get value and store in register
                // get method info
                TableRow * classRow = lookupClassInfo(method);
                if (classRow == NULL)
                    return;
                // check if class var or method arg/var
                bool isInClass = false;
                bool isInMethod = false;
                // get method info
                TableRow * methodRow = lookupMethodInfo(classRow->table, method);
                if (methodRow == NULL)
                    return;
                int argcount = methodRow->methodInfo->argCount;
                // Check if class has symbol
                TableRow * info = classRow->table->getSymbolInfo(code->strAddress[1]);
                if (info == NULL) {
                    // doesn't exist in class
                    isInMethod = true;
                    // get symbol from method
                    info = methodRow->table->getSymbolInfo(code->strAddress[1]);
                    if (info == NULL) {
                        cout << "Failed Symbol Table lookup for " << code->strAddress[1] << " in compileSet" << endl;
                        return;
                    }
                }
                else {
                    // exists in class
                    isInClass = true;
                }
                // calculate offset to object
                int absOffset = 0;
                if (isInClass)
                    absOffset = info->varInfo->offset;
                else {
                    if (info->symbolType == SARG)
                        absOffset = info->argInfo->offset;
                    else {
                        // calculate offset: [argcount * 2] + 4 + 4 + reloffset
                        int relOffset = absOffset;
                        absOffset = (argcount * 4);
                        if (absOffset == 0)
                            absOffset += 4;
                        absOffset += 4;
                        absOffset += relOffset;
                    }
                }
                // get value off of stack and load into registers
                string instruction = string("MOV r10, r9");
                addInstruction(instruction);
                if (isInClass) {
                    // load obj ref from stack
                    int objoffset = argcount * 4;
                    instruction = string("SUB r10, r10, #") + to_string(objoffset);
                    addInstruction(instruction);
                    instruction = string("LDR r10, [r10]");
                    addInstruction(instruction);
                }
                if (isInClass)
                    instruction = string("ADD r10, r10, #") + to_string(absOffset);
                else
                    instruction = string("SUB r10, r10, #") + to_string(absOffset);
                addInstruction(instruction);
                instruction = string("LDR ") + code->strAddress[0] + ", [r10]";
                addInstruction(instruction);
            }
        }
        else {
            // unary
            switch (code->op) {
                case Not: {
                    if (code->types[1] == IntLiteral) {
                        // move to destination address before proceeding
                        string instruction = string("MOV ") + result + ", #" + to_string(code->intAddress[1]);
                        addInstruction(instruction);
                    }
                    // cmp first
                    string instruction = string("CMP ") + result + ", #0";
                    addInstruction(instruction);
                    // make true if false
                    instruction = string("MOVEQ ") + result + ", #1";
                    addInstruction(instruction);
                    // make false if true
                    instruction = string("MOVNE ") + result + ", #0";
                    addInstruction(instruction);
                    break;
                }
                case Add: {
                    string instruction;
                    if (code->types[1] == IntLiteral) {
                        // result <- intLiteral
                        instruction = string("MOV ") + result + ", #" + to_string(code->intAddress[1]); 
                    }
                    else {
                        // result <- x
                        if (result.compare(code->strAddress[1]) == 0)
                            break;      // ignore the instruction
                        else
                            instruction = string("MOV ") + result + ", " + code->strAddress[1];
                    }
                    addInstruction(instruction);
                    break;
                }
                case Sub: {
                    if (code->types[1] == IntLiteral) {
                        // move to destination address before proceeding
                        string instruction = string("MOV ") + result + ", #" + to_string(code->intAddress[1]);
                        addInstruction(instruction);
                    }
                    // negate the value
                    string instruction = string("NEG ") + result;
                    addInstruction(instruction);
                    break;
                }
            }
        }
    }
    else {
        string result = code->strAddress[0];
        if (code->types[1] == IntLiteral) {
            // move value to register first
            string base = string("MOV ") + "r10";
            base += ", #" + to_string(code->intAddress[1]);
            addInstruction(base);
            code->types[1] = Reg;
            code->strAddress[1] = string("r10");
        }
        switch (code->op) {
            case Add: {
                string base = string("ADD ") + result + ", ";
                if (code->types[1] == IntLiteral)
                    base += result;
                else
                    base += code->strAddress[1];
                base += ", ";
                if (code->types[2] == IntLiteral)
                    base += "#" + to_string(code->intAddress[2]);
                else
                    base += code->strAddress[2];
                addInstruction(base);
                break;
            }
            case Sub: {
                string base = string("SUB ") + result + ", ";
                if (code->types[1] == IntLiteral)
                    base += result;
                else
                    base += code->strAddress[1];
                base += ", ";
                if (code->types[2] == IntLiteral)
                    base += "#" + to_string(code->intAddress[2]);
                else
                    base += code->strAddress[2];
                addInstruction(base);
                break;
            }
            case Mul: {
                string base = string("MUL ") + result + ", ";
                if (code->types[1] == IntLiteral)
                    base += result;
                else
                    base += code->strAddress[1];
                base += ", ";
                if (code->types[2] == IntLiteral)
                    base += "#" + to_string(code->intAddress[2]);
                else
                    base += code->strAddress[2];
                addInstruction(base);
                break;
            }
            case Equal: {
                // compare the numbers first
                string base = string("CMP ");
                if (code->types[1] == IntLiteral)
                    base += result;
                else
                    base += code->strAddress[1];
                base += ", ";
                if (code->types[2] == IntLiteral)
                    base += "#" + to_string(code->intAddress[2]);
                else
                    base += code->strAddress[2];
                addInstruction(base);
                // if equal, set value to 1
                base = string("MOVEQ ") + result + ", #1";
                addInstruction(base);
                // if not equal, set value to 0
                base = string("MOVNE ") + result + ", #0";
                addInstruction(base);
                break;
            }
            case GreaterThan: {
                // compare the numbers first
                string base = string("CMP ");
                if (code->types[1] == IntLiteral)
                    base += result;
                else
                    base += code->strAddress[1];
                base += ", ";
                if (code->types[2] == IntLiteral)
                    base += "#" + to_string(code->intAddress[2]);
                else
                    base += code->strAddress[2];
                addInstruction(base);
                // if greater than, set value to 1
                base = string("MOVGT ") + result + ", #1";
                addInstruction(base);
                // if lessthanorequal to, set value to 0
                base = string("MOVLE ") + result + ", #0";
                addInstruction(base);
                break;
            }
            case GreaterThanEqual: {
                // compare the numbers first
                string base = string("CMP ");
                if (code->types[1] == IntLiteral)
                    base += result;
                else
                    base += code->strAddress[1];
                base += ", ";
                if (code->types[2] == IntLiteral)
                    base += "#" + to_string(code->intAddress[2]);
                else
                    base += code->strAddress[2];
                addInstruction(base);
                // if greater than, set value to 1
                base = string("MOVGE ") + result + ", #1";
                addInstruction(base);
                // if lessthanorequal to, set value to 0
                base = string("MOVLT ") + result + ", #0";
                addInstruction(base);
                break;
            }
            case LessThan: {
                // compare the numbers first
                string base = string("CMP ");
                if (code->types[1] == IntLiteral)
                    base += result;
                else
                    base += code->strAddress[1];
                base += ", ";
                if (code->types[2] == IntLiteral)
                    base += "#" + to_string(code->intAddress[2]);
                else
                    base += code->strAddress[2];
                addInstruction(base);
                // if greater than, set value to 1
                base = string("MOVLT ") + result + ", #1";
                addInstruction(base);
                // if lessthanorequal to, set value to 0
                base = string("MOVGE ") + result + ", #0";
                addInstruction(base);
                break;
            }
            case LessThanEqual: {
                // compare the numbers first
                string base = string("CMP ");
                if (code->types[1] == IntLiteral)
                    base += result;
                else
                    base += code->strAddress[1];
                base += ", ";
                if (code->types[2] == IntLiteral)
                    base += "#" + to_string(code->intAddress[2]);
                else
                    base += code->strAddress[2];
                addInstruction(base);
                // if greater than, set value to 1
                base = string("MOVLE ") + result + ", #1";
                addInstruction(base);
                // if lessthanorequal to, set value to 0
                base = string("MOVGT ") + result + ", #0";
                addInstruction(base);
                break;
            }
            case And: {
                // compare the numbers first
                string base = string("AND ") + result + ", ";
                if (code->types[1] == IntLiteral)
                    base += result;
                else
                    base += code->strAddress[1];
                base += ", ";
                if (code->types[2] == IntLiteral)
                    base += "#" + to_string(code->intAddress[2]);
                else
                    base += code->strAddress[2];
                addInstruction(base);
                break;
            }
            case Or: {
                // compare the numbers first
                string base = string("ORR ") + result + ", ";
                if (code->types[1] == IntLiteral)
                    base += result;
                else
                    base += code->strAddress[1];
                base += ", ";
                if (code->types[2] == IntLiteral)
                    base += "#" + to_string(code->intAddress[2]);
                else
                    base += code->strAddress[2];
                addInstruction(base);
                break;
            }
        }
    }
}
void Compiler::compileSetNew(AddressCode * code, Method * method) {
    string result = code->strAddress[0];
    string instruction;
    // type r1 <- new int
    if (peekNextInstruction()->type == CARR) {
        // allocate new array
        AddressCode * nextInstruction = consumeNextInstruction();
        if (nextInstruction->addressCount == 2) {
            if (nextInstruction->types[1] == IntLiteral) {
                int size = nextInstruction->intAddress[1] + 1;
                instruction = string("MOV r0, #") + to_string(size * 4);
                addInstruction(instruction);
                // call malloc
                pushLinkRegister();
                instruction = string("BL malloc");
                addInstruction(instruction);
                popLinkRegister();
                // move to result
                instruction = string("MOV ") + code->strAddress[0] + ", r0";
                addInstruction(instruction);
                // set size 
                // move immediate to scratch register
                instruction = string("MOV r10, #") + to_string(size-1);
                addInstruction(instruction);
                instruction = string("STR r10, [r0]");
                addInstruction(instruction);
                info.isArray = true;
                info.isInit = true;
            }
            else {
                // move result to r0
                instruction = string("MOV r0, ") + nextInstruction->strAddress[1];
                addInstruction(instruction);
                // add metadata size
                instruction = string("ADD r0, r0, #1");
                addInstruction(instruction);
                // move immediate to scratch because MOV can't have immediates
                instruction = string("MOV r10, #4");
                addInstruction(instruction);
                // multiply by align size
                instruction = string("MUL r0, r0, r10");
                addInstruction(instruction);
                // save size register
                instruction = string("MOV r10, ") + nextInstruction->strAddress[1];
                addInstruction(instruction);
                // call malloc
                pushLinkRegister();
                instruction = string("BL malloc");  // malloc occupies 0-2
                addInstruction(instruction);
                popLinkRegister();
                // move to result
                instruction = string("MOV ") + code->strAddress[0] + ", r0";
                addInstruction(instruction);
                // store size
                instruction = string("STR r10, [r0]");
                addInstruction(instruction);
                info.isArray = true;
                info.isInit = true;
            }
        }
        else {
            //2d array
            if (nextInstruction->types[1] == IntLiteral && nextInstruction->types[2] == IntLiteral) {
                int size = nextInstruction->intAddress[1] * nextInstruction->intAddress[2];
                size += 2;      // metadata size
                instruction = string("MOV r0, #") + to_string(size * 4);
                addInstruction(instruction);
                pushLinkRegister();
                instruction = string("BL malloc");
                addInstruction(instruction);
                popLinkRegister();
                instruction = string("MOV ") + code->strAddress[0] + ", r0";
                addInstruction(instruction);
                // move immediate to scratch register
                instruction = string("MOV r10, #") + to_string(nextInstruction->intAddress[1]);
                addInstruction(instruction);
                instruction = string("STR r10, [r0]");
                addInstruction(instruction);
                instruction = string("MOV r10, #") + to_string(nextInstruction->intAddress[2]);
                addInstruction(instruction);
                instruction = string("ADD r0, r0, #4");
                addInstruction(instruction);
                instruction = string("STR r10, [r0]");
                addInstruction(instruction);
                info.isArray = true;
                info.isInit = true;
            }
            else if (nextInstruction->types[1] == Reg && nextInstruction->types[2] == Reg) {
                // calculate size
                instruction = string("MOV r0, ") + nextInstruction->strAddress[1];
                addInstruction(instruction);
                instruction = string("MUL r0, r0, ") + nextInstruction->strAddress[2];
                addInstruction(instruction);
                instruction = string("ADD r0, r0, #2");
                addInstruction(instruction);
                // save registers first one r10, second r5
                instruction = string("MOV r10, ") + nextInstruction->strAddress[1];
                addInstruction(instruction);
                instruction = string("MOV r5, ") + nextInstruction->strAddress[2];
                addInstruction(instruction);
                pushLinkRegister();
                instruction = string("BL malloc");
                addInstruction(instruction);
                popLinkRegister();
                instruction = string("MOV ") + code->strAddress[0] + ", r0";
                addInstruction(instruction);
                instruction = string("STR r10, [r0]");
                addInstruction(instruction);
                instruction = string("ADD r0, r0, #4");
                addInstruction(instruction);
                instruction = string("STR r5, [r0]");
                addInstruction(instruction);
                info.isArray = true;
                info.isInit = true;
            }
            else {
                // one of them is a register
                if (nextInstruction->types[1] == Reg) {

                }
                else {

                }
            }
        }
    }
    else {
        // allocate new object
        TableRow * classInfo = lookupClassInfo(code->strAddress[1]);
        if (classInfo == NULL)
            return;
        int allocateSize = classInfo->classInfo->classSize;
        if (allocateSize == 0)
            allocateSize = 4;   // burn all the memory
        instruction = string("MOV r0, #") + to_string(allocateSize);
        addInstruction(instruction);
        pushLinkRegister();
        instruction = string("BL malloc");
        addInstruction(instruction);
        popLinkRegister();
        instruction = string("MOV ") + result + ", r0";
        addInstruction(instruction);
        // save context about new object
        info.className = code->strAddress[1];
        info.isArray = false;
        info.isInit = true;
        info.isClass = true;
    }
}
void Compiler::addInstruction(string instruction) {
    if (useTab)
        instruction = "\t" + instruction;
    instructions->push_back(instruction);
    curlineno++;
}
void Compiler::addInstruction(const char * str) {
    addInstruction(string(str));
}
int parseRegisterTarget(string reg) {
    return reg[1] - '0';
}
TableRow * Compiler::lookupMethodInfo(SymbolTable * classTable, Method * method) {
    string className = method->getClassName();
    string parentName = method->getParentName();
    parentName = Method::fixMethodName(className, parentName);
    TableRow * methodInfo = classTable->getMethodInfo(parentName);
    if (methodInfo == NULL) {
        cout << "Failed Symbol Table lookup for " << parentName << " in lookupMethodInfo" << endl;
        return NULL;
    }
    return methodInfo;
}
TableRow * Compiler::lookupClassInfo(Method * method) {
    TableRow * classRow = program->symbolTable->getSymbolInfo(method->getClassName());
    if (classRow == NULL) {
        cout << "Failed Symbol Table lookup for " << method->getClassName() << " in lookupClassInfo" << endl;
        return NULL;
    }
    return classRow;
}
TableRow * Compiler::lookupClassInfo(string className) {
    TableRow * classRow = program->symbolTable->getSymbolInfo(className);
    if (classRow == NULL) {
        cout << "Failed Symbol Table lookup for " << className << " in lookupClassInfo" << endl;
        return NULL;
    }
    return classRow;
}
AddressCode * Compiler::peekNextInstruction() {
    return currentMethod->instructions[currentInstructionCount + 1];
}
AddressCode * Compiler::consumeNextInstruction() {
    AddressCode * code = currentMethod->instructions[currentInstructionCount + 1];
    currentInstructionCount++;
    return code;
}
void Compiler::pushLinkRegister() {
    if (!currentMethod->isMain())
        addInstruction("PUSH {lr}");
}
void Compiler::popLinkRegister() {
    if (!currentMethod->isMain())
        addInstruction("POP {lr}");
}