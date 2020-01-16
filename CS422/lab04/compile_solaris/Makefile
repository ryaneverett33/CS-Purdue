# Makefile for Computer Networks and Internets TCP API
# Solaris Version

DEFS	= -DSOLARIS
INC_DIR	= ../h
INCLUDE = -I$(INC_DIR)
LD	= ld
CC	= gcc
LIBS	= -lsocket  -pthread
FLAGS   = -c -g


API_OBJ = $(API_SRC:.c=.o)

APP_DIR = ../apps
APP_SRC =	pingserver.c		\
		pingclient.c		\
		global.c

APP_OBJ = $(APP_SRC:.c=.o)
APP_EXE = pingserver pingclient

CFILES = $(API_DIR)/*.c $(APP_DIR)/*.c

apps: $(APP_EXE)

pingserver: pingserver.o global.o
	$(CC) -o $@ $(LIBS)  pingserver.o global.o
pingclient: pingclient.o global.o
	$(CC) -o $@ $(LIBS)  pingclient.o global.o


$(APP_OBJ):
	$(CC) -c $(INCLUDE) $(FLAGS) $(DEFS) $(APP_DIR)/$(@:.o=.c)
$(CNAIAPI_LIB): $(API_OBJ)
	$(LD) -r -o $(CNAIAPI_LIB) $(API_OBJ)
$(API_OBJ):
	$(CC) $(INCLUDE) $(FLAGS) $(DEFS) $(API_DIR)/$(@:.o=.c)

clean:
	\rm -rf *.o  $(APP_EXE)

# Application Dependancies
pingclient.o: $(APP_DIR)/pingclient.c $(INC_DIR)/global.h 
pingserver.o: $(APP_DIR)/pingserver.c $(INC_DIR)/global.h
global.o: $(APP_DIR)/global.c

