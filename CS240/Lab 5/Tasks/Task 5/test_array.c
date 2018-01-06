
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "array.h"

double a[] = {4, 7, 2, 6, 1, 8, 9, 2, 11, -1, 3, 12};
int n = sizeof(a)/sizeof(double);

void test1() {
  double s = sumArray(n, a);
  printf("sumArray1=%lf\n", s);
  s = sumArray(-1, a);
  printf("sumArray2=%lf\n", s);
  s = sumArray(-100, a);
  printf("sumArray3=%lf\n", s);
  s = sumArray(100, NULL);
  printf("sumArray4=%lf\n", s);
}

void test2() {
  double s = maxArray(n, a);
  printf("maxArray1=%lf\n", s);
  s = maxArray(-100, a);
  printf("maxArray2=%lf\n", s);
  s = maxArray(100, NULL);
  printf("maxArray3=%lf\n", s);
}

void test3() {
  double s = minArray(n, a);
  printf("minArray1=%lf\n", s);
  s = minArray(-100, a);
  printf("minArray2=%lf\n", s);
  s = minArray(1, NULL);
  printf("minArray3=%lf\n", s);
}

void test4() {
  int i = findArray(n, a, 8.5, 10);
  printf("findArray1=%d\n", i);
  i = findArray(-11, a, 8.5, 10);
  printf("findArray2=%d\n", i);
  i = findArray(3, NULL, 8.5, 10);
  printf("findArray3=%d\n", i);
}

void test5() {
  printArray(n, a);
  printArray(-1, a);
  printArray(n, NULL);
}

void test6() {
  printArray(n, a);
  printf("-----------\n");
  reverseArray(n,a);
  printArray(n, a);
  printf("-----------\n");
  reverseArray(-5,a);
  printArray(n, a);
  printf("-----------\n");
  reverseArray(n, NULL);
  printArray(n, a);
}

int main(int argc, char ** argv) {

  char * test;
  
  if (argc <2) {
    printf("Usage: test_array test1|test2|test3|test4|test5|test6\n");
    exit(1);
  }
  
  test = argv[1];
  printf("Running %s\n", test);
  if (strcmp(test, "test1")==0) {
    test1();
  }
  else if (strcmp(test, "test2")==0) {
    test2();
  }
  else if (strcmp(test, "test3")==0) {
    test3();
  }
  else if (strcmp(test, "test4")==0) {
    test4();
  }
  else if (strcmp(test, "test5")==0) {
    test5();
  }
  else if (strcmp(test, "test6")==0) {
    test6();
  }
  else {
    printf("Test not found!!n");
    exit(1);
  }
  
  return 0;
}

