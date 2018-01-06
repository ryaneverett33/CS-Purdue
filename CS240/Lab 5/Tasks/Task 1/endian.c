#include <stdio.h>
#include <stdlib.h>

int isBigEndian() {
	// Find first byte
	int num = 1;
    char * point = (char *)&num;
	/*printf("point1 = %d\n", (int)*point);
	point++;
	printf("point2 = %d\n", (int)*point);
	point++;
	printf("point3 = %d\n", (int)*point);
	point++;
	printf("point4 = %d\n", (int)*point);*/
	if ((int)*point == num) {
		return 0;
	}
	else {
		return 1;
	}
}

int main()
{
	if (isBigEndian()) {
		printf("Machine is Big Endian\n");
	}
    else {
		printf("Machine is Little Endian\n");
	}
    return 0;
}
