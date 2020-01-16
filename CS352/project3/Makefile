mjavac: y.tab.cc lex.yy.c mjavac.cc ast.cc ast.hh statement.cc expression.cc symboltable.hh symboltable.cc compile.hh 3ac.cc converter.cc compiler.cc
	g++ -g -Dlib ast.cc symboltable.cc statement.cc expression.cc y.tab.cc lex.yy.c converter.cc 3ac.cc compiler.cc mjavac.cc -o mjavac
# lib:
# http://docencia.ac.upc.edu/FIB/USO/Bibliografia/unix-c-libraries.html
parser: y.tab.c lex.yy.c
	gcc y.tab.c lex.yy.c -o parser
y.tab.cc: parser.y
	bison --debug -d -g --verbose parser.y -o y.tab.cc
lex.yy.c: parser.l
	flex -d -o lex.yy.c parser.l
clean:
	rm -f lex.yy.c y.tab.cc parser typechecker mjavac