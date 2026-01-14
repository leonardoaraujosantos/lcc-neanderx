/*
 * Control flow test program for NEANDER-X LCC backend
 *
 * Tests if/else, while loops, and function calls.
 */

/* Absolute value function */
char abs_val(char x) {
    if (x < 0) {
        return -x;
    }
    return x;
}

/* Maximum of two values */
char max(char a, char b) {
    if (a > b) {
        return a;
    } else {
        return b;
    }
}

/* Sum from 1 to n using a loop */
char sum_to_n(char n) {
    char sum = 0;
    char i = 1;

    while (i <= n) {
        sum = sum + i;
        i = i + 1;
    }

    return sum;
}

/* Factorial function (recursive) */
char factorial(char n) {
    if (n <= 1) {
        return 1;
    }
    return n * factorial(n - 1);
}

/* Main function */
char main(void) {
    char a = -5;
    char b = 10;
    char result;

    /* Test abs_val: |-5| = 5 */
    result = abs_val(a);

    /* Test max: max(5, 10) = 10 */
    result = max(result, b);

    /* Test sum_to_n: 1+2+3+4+5 = 15 */
    result = sum_to_n(5);

    /* Test factorial: 5! = 120 */
    result = factorial(5);

    return result;  /* Should return 120 */
}
