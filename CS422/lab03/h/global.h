/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   global.h
 * Author: abc1986
 *
 * Created on September 8, 2018, 3:49 PM
 */

#ifndef GLOBAL_H
#define GLOBAL_H
#define PROMPT_BUFFER_SIZE 50
#define STDIN_FILENO  0         //from cnaiapi_win32.h
#define STDOUT_FILENO 1         //from cnaiapi_win32.h
#define BACKLOG 10
#define MAX_FILE_LEN 1024
#define MAX_FILETABLE_SIZE 5   //only 20 open files at once

enum Commands {
    OPEN,
    READ,
    BACK,
    CLOS,
    INVALID         //catch all for invalid commands
};
struct prompt_res {
    enum Commands command;
    char * filename;        //OPEN testfile1.txt for example
    int filenameLen;        //length of file name
    int argument;           //READ 10 for example
};
struct file_table_entry {
    char * filename;
    FILE * file;
    int filesize;
    int currentOffset;
};

enum Commands parseCommand(char * string, int len); 
int readln (char *buff, int buffsz);
int getIntArgument(char * string, int stringLen);
int getStringLen(char * string);
int getIntLength(int value);
bool isValidRequest(struct prompt_res*);
int getFileSize(char * filename);
bool doesFileExist(char * filename);
bool isFilenameEqual(char * filename1, char * filename2);
//int ClampLower(int lowerbound, int value);

#endif /* GLOBAL_H */
