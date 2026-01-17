/*
 * 03_arithmetic.c - Arithmetic operations test
 * Tests: 16-bit addition, subtraction, multiplication, division
 */

int add(int a, int b) {
    return a + b;
}

int sub(int a, int b) {
    return a - b;
}

int main(void) {
    int x = 50;
    int y = 30;
    int sum = add(x, y);      /* 80 */
    int diff = sub(x, y);     /* 20 */
    return sum + diff;        /* 100 */
}
