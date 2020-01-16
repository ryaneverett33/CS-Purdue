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
#include <stdint.h>
#include <sys/time.h>
#ifndef GLOBAL_H
#define GLOBAL_H
#define MAX_NUM_HOSTS 12

struct host_table_entry {
    char * hostname;
    char * ip_addr;                    //resolved by getIpAddress();
    struct timeval timestamp;          //when the when the request was sent
};
uint32_t serialize(uint32_t value);
uint32_t deserialize(uint32_t value);
int setup(char * port);
uint32_t clientPayload();
uint32_t serverPayload();
int time_diff(struct timeval old, struct timeval current);

#endif /* GLOBAL_H */
