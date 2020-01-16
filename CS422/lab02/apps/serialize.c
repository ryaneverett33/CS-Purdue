#include "c_msg.h"
#include <netinet/in.h>
#include <stdint.h>

/*char * serializeInt(int value, char * buffer) {
    uint32_t fixedValue = htonl((uint32_t)value);
    buffer[0] = fixedValue;
    buffer[1] = fixedValue >> 8;
    buffer[2] = fixedValue >> 16;
    buffer[3] = fixedValue >> 24;
    return buffer += 4;
}
int deserializeInt(char * buffer) {
    uint32_t value;
    value = buffer[0];
    value >> 8 = buffer[1];
    value >> 16 = buffer[2];
    value >> 24 = buffer[3];
    return (int)ntohl(value);
}*/
int serializeInt(int value) {
    return (int)htonl((uint32_t)value);
}
int deserializeInt(int value) {
    return (int)ntohl((uint32_t)value);
}
/*char * serializeString(char * string, char * buffer) {
    //assuming string is the length of C_FILENAME_LEN;
    buffer[0] = string;
    buffer += C_FILENAME_LEN;
}
//hard-coded, since 
int calculateBufferSize() {
    int size = 0;
    size += sizeof(int);        //mtype
    size += sizeof(char * C_FILENAME_LEN)   //filename
    size += sizeof(int);        //maxsize
    size += sizeof(int);        //actualsize
    return size;
}*/
struct c_msg serialize(struct c_msg msg) {
    //buffer is a binary buffer, nothing fancy like json or xml
    //char * buffer = (char *)malloc(sizeof(char) * calculateBufferSize());
    /*char * pointer = buffer;    //move the placement of the pointer, not the actual buffer
    //int index = 0;

    //place elements
    pointer = serializeInt(msg.mtype);
    pointer = serializeString(msg.filename);
    pointer = serializeInt(msg.maxsize);
    pointer = serializeInt(msg.actualsize);

    return buffer;*/
    struct c_msg tmpMessage = msg;
    tmpMessage.mtype = serializeInt(msg.mtype);
    tmpMessage.maxsize = serializeInt(msg.maxsize);
    tmpMessage.actualsize = serializeInt(msg.actualsize);
    return tmpMessage;
}
struct c_msg deserialize(struct c_msg msg) {
    /*if (DEBUG)
        printf("deserialize on length: %d, struct length: %d\n", len, calculateBufferSize());
    char * pointer = buff;
    msg.mtype = deserializeInt()*/
    struct c_msg tmpMessage = msg;
    tmpMessage.mtype = deserializeInt(msg.mtype);
    tmpMessage.maxsize = deserializeInt(msg.maxsize);
    tmpMessage.actualsize = deserializeInt(msg.actualsize);
    return tmpMessage;
}
//fills the filename array in the struct from a pointer
//basically a copy
void fillFileName(char * filename, struct c_msg msg) {
    for (int i = 0; i < C_FILENAME_LEN; i++) {
        if (filename[i] != 0)
            msg.filename[i] = filename[i];
    }
}