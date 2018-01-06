
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "mystring.h"

// Type "man string" to see what every function expects.

int mystrlen(char * s) {
	int i = 0;
	while (s[i] != '\0') {
		i++;
	}
	return i;
}

char * mystrcpy(char * dest, char * src) {
	dest = src;
	int len = mystrlen(src);
	printf("%i", len);
	dest = malloc(200);
	int i = 0;
	if (len == 0) {
		dest = src;
		return dest;
	}
	
	for (i = 0; i < len; i++) {
		printf("*");
		dest[i] = src[i];
	}
	printf("\n");	
	return dest;
}

char * mystrcat(char * dest, char * src) {
	int srclen = mystrlen(src);
	int destlen = mystrlen(dest);
	int i = 0;
	for (i = 0; i < srclen && i < destlen; i++) {
		dest[i] = src[i];
	}
	return dest;
}

int mystrcmp(char * s1, char * s2) {
	int i;
	int loop = 0;
	int len1 = mystrlen(s1);
	int len2 = mystrlen(s2);
	if (len1 > len2) return 1;
	else if (len2 > len1) return -1;
	else loop = len1;
	for (i = 0; i < loop; i++) {
		if (s1[i] > s2[i]) return 1;
		if (s1[i] < s2[i]) return -1;
	}
	
	return 0;
}

char * mystrstr(char * hay, char * needle) {
	int i;
	int j = 0;
	int haylen = mystrlen(hay);
	int needlelen = mystrlen(needle);	
	//int BoolCheck = 0;
	for (i = 0; i < haylen; i++) {
		if (hay[i] == needle[0]) {
			//for (j = 1; hay[j] == needle[j]; j++) { }
			for (j = 1; hay[i] == needle[j]; j++) {
			}
			if (j > (needlelen - 1)) {
				return (hay + i);
			}
		}
	}
	return NULL;
}

char * mystrdup(char * s) {
	int len = mystrlen(s);
	char* dup = (char*)malloc((len) * sizeof(char));
	int i;
	for (i = 0; i < len; i++) {
		dup[i] = s[i];
	}
	return s;
}

char * mymemcpy(char * dest, char * src, int n)
{
	int len = mystrlen(src);
	int i;
	for (i = 0; i < len; i++) {
		dest[i] = src[i];
	}
	return dest;
}

