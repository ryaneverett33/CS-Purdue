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
APP_SRC =	pingserver.c		\
		pingclient.c		\
		global.c


APP_OBJ = $(APP_SRC:.c=.o)
APP_EXE = pingserver pingclient

CFILES = $(APP_DIR)/*.c

apps: $(APP_EXE)

pingserver: global.o pingserver.o
	$(CC) -o $@ $(LIBS) global.o pingserver.o
pingclient: global.o pingclient.o
	$(CC) -o $@ $(LIBS) global.o pingclient.o


$(APP_OBJ):
	$(CC) -c $(INCLUDE) $(FLAGS) $(DEFS) $(APP_DIR)/$(@:.o=.c)


clean:
	\rm -rf *.o core $(CNAIAPI_LIB) $(APP_EXE)



# Application Dependancies
pingclient.o: $(APP_DIR)/pingclient.c $(INC_DIR)/global.h
pingserver.o: $(APP_DIR)/pingserver.c $(INC_DIR)/global.h
global.o: $(APP_DIR)/global.c 
