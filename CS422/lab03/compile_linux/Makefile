# Makefile for Comer CNAI Simple TCP API
# Linux Version

DEFS	= -DLINUX
INC_DIR	= ../h
INCLUDE = -I$(INC_DIR)
LD	= ld
CC	= gcc
LIBS	= -pthread
FLAGS   = -c -g




APP_DIR = ../apps
APP_SRC =	server.c		\
		client.c		\
		global.c


APP_OBJ = $(APP_SRC:.c=.o)
APP_EXE = server client

CFILES = $(APP_DIR)/*.c

apps: $(APP_EXE)

server: global.o server.o
	$(CC) -o $@ $(LIBS) global.o server.o
client: global.o client.o
	$(CC) -o $@ $(LIBS) global.o client.o


$(APP_OBJ):
	$(CC) -c $(INCLUDE) $(FLAGS) $(DEFS) $(APP_DIR)/$(@:.o=.c)


clean:
	\rm -rf *.o core $(CNAIAPI_LIB) $(APP_EXE)



# Application Dependancies
client.o: $(APP_DIR)/client.c $(INC_DIR)/global.h
server.o: $(APP_DIR)/server.c $(INC_DIR)/global.h
global.o: $(APP_DIR)/global.c 
