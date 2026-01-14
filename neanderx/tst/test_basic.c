/*
 * Basic test program for NEANDER-X LCC backend
 *
 * This program tests basic C constructs on the 8-bit processor.
 * Expected result: returns 8 (5 + 3)
 */

/* Global variable */
char global_val = 3;

/* Simple addition function */
char add(char a, char b) {
    return a + b;
}

/* Test arithmetic operators */
char test_arithmetic(void) {
    char x = 10;
    char y = 3;
    char result;

    result = x + y;   /* 13 */
    result = result - 5;  /* 8 */

    return result;
}

/* Main function */
char main(void) {
    char a = 5;
    char b;
    char sum;

    b = global_val;
    sum = add(a, b);

    return sum;  /* Should return 8 */
}
