CXX = g++ -fPIC -pthread -fno-stack-protector -g
NETLIBS= -lnsl -ldl

all: git-commit myhttpd daytime-server use-dlopen hello.so

daytime-server : daytime-server.o
	$(CXX) -o $@ $@.o $(NETLIBS)

myhttpd : myhttpd.o FileInfo.o Sender.o HtmlMaker.o CgiRunner.o Stats.o Logger.o
	echo "Building rull myhttpd"
	$(CXX) -o $@ FileInfo.cc Sender.cc HtmlMaker.cc CgiRunner.cc Stats.cc Logger.cc $@.o $(NETLIBS)

use-dlopen: use-dlopen.o
	$(CXX) -o $@ $@.o $(NETLIBS)

hello.so: hello.o
	ld -G -o hello.so hello.o

%.o: %.cc
	echo "building rule .c"
	@echo 'Building $@ from $<'
	$(CXX) -o $@ -c -I. $<

.PHONY: git-commit
git-commit:
	git checkout
	git add *.cc *.h Makefile >> .local.git.out  || echo
	git commit -a -m 'Commit' >> .local.git.out || echo
	git push origin master 

.PHONY: clean
clean:
	rm -f *.o use-dlopen hello.so
	rm -f *.o daytime-server myhttpd

