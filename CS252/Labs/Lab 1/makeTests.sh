#/bin/bash

FLAGS = --std=gnu11 -Wall

echo "Building empty"

gcc $FLAGS -g -o empty empty.c MyMalloc.c


echo "Building test33"

gcc $FLAGS -g -o test33 test33.c MyMalloc.c

echo "Building Left Size Test"

gcc $FLAGS -g -o leftSizeTest leftSizeTest.c MyMalloc.c

echo "Building alloc3"

gcc $FLAGS -g -o alloc3 alloc3.c MyMalloc.c

echo "Building freeTest.c"

gcc $FLAGS -g -o freeTest freeTest.c MyMalloc.c

echo "Building testCreateOne"

gcc $FLAGS -g -o createOne testCreateOne.c MyMalloc.c

echo "Build complete"
