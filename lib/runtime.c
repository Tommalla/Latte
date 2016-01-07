/* Tomasz Zakrzewski, tz336079, 2015-2016                             /
/  Library functions implementation for the Latte language compiler. */
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

extern void printInt(int a) {
    printf("%d", a);
}

extern void printString(const char* str) {
    printf("%s", str);
}

void error() {
    printf("runtime error");
    exit(1);
}

int readInt() {
    int a;
    scanf("%d", &a);
    return a;
}

char* readString() {
    char* res = (char*)malloc(10);
    size_t len;
    getline(&res, &len, stdin); 
    return res;
}
