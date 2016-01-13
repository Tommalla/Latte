/* Tomasz Zakrzewski, tz336079, 2015-2016                             /
/  Library functions implementation for the Latte language compiler. */
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

extern void printInt(int a) {
    printf("%d\n", a);
}

extern void printString(const char* str) {
    printf("%s\n", str);
}

void error() {
    printf("runtime error");
    exit(1);
}

int readInt() {
    int a;
    scanf("%d\n", &a);
    return a;
}

char* readString() {
    char* res = (char*)malloc(10);
    size_t len;
    getline(&res, &len, stdin);
    len = strlen(res);
    res[len - 1] = '\0';
    return res;
}

char* __concatStrings(char* a, char* b) {
    size_t lenA, lenB;
    lenA = strlen(a);
    lenB = strlen(b);
    char* res = malloc(lenA + lenB + 1);
    memcpy(res, a, lenA);
    memcpy(res + lenA, b, lenB);
    res[lenA + lenB] = '\0';
    return res;
}
