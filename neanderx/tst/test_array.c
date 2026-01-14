/*
 * Array and multiplication test program for NEANDER-X LCC backend
 *
 * Tests array access, multiplication, division, and modulo.
 */

/* Global array */
char data[5] = {1, 2, 3, 4, 5};

/* Sum array elements */
char sum_array(char *arr, char len) {
    char sum = 0;
    char i;

    for (i = 0; i < len; i = i + 1) {
        sum = sum + arr[i];
    }

    return sum;
}

/* Test multiplication */
char test_mul(char a, char b) {
    return a * b;
}

/* Test division */
char test_div(char a, char b) {
    return a / b;
}

/* Test modulo */
char test_mod(char a, char b) {
    return a % b;
}

/* Main function */
char main(void) {
    char arr[3];
    char result;
    char mul_result;
    char div_result;
    char mod_result;

    /* Initialize local array */
    arr[0] = 10;
    arr[1] = 20;
    arr[2] = 30;

    /* Test sum_array: 10 + 20 + 30 = 60 */
    result = sum_array(arr, 3);

    /* Test multiplication: 6 * 7 = 42 */
    mul_result = test_mul(6, 7);

    /* Test division: 42 / 6 = 7 */
    div_result = test_div(42, 6);

    /* Test modulo: 17 % 5 = 2 */
    mod_result = test_mod(17, 5);

    /* Combine results */
    result = div_result + mod_result;  /* 7 + 2 = 9 */

    return result;  /* Should return 9 */
}
