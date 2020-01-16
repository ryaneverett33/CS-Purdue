# Makefile for Computer Networks and Internets TCP API
# Solaris Version

DEFS	= -DSOLARIS
INC_DIR	= ../h
INCLUDE = -I$(INC_DIR)
LD	= ld
CC	= gcc
LIBS	= -pthread
FLAGS   = -c -g


API_OBJ = $(API_SRC:.c=.o)

APP_DIR = ../apps
APP_SRC =	server.c		\
		client.c		\
		global.c

APP_OBJ = $(APP_SRC:.c=.o)
APP_EXE = server client

CFILES = $(API_DIR)/*.c $(APP_DIR)/*.c

apps: $(APP_EXE)

server: server.o global.o
	$(CC) -o $@ $(LIBS)  server.o global.o
client: client.o global.o
	$(CC) -o $@ $(LIBS)  client.o global.o


$(APP_OBJ):
	$(CC) -c $(INCLUDE) $(FLAGS) $(DEFS) $(APP_DIR)/$(@:.o=.c)
$(CNAIAPI_LIB): $(API_OBJ)
	$(LD) -r -o $(CNAIAPI_LIB) $(API_OBJ)
$(API_OBJ):
	$(CC) $(INCLUDE) $(FLAGS) $(DEFS) $(API_DIR)/$(@:.o=.c)

clean:
	\rm -rf *.o core  $(APP_EXE)

# Application Dependancies
client.o: $(APP_DIR)/client.c $(INC_DIR)/global.h 
server.o: $(APP_DIR)/server.c $(INC_DIR)/global.h
global.o: $(APP_DIR)/global.c

