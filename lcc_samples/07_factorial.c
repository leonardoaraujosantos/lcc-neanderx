/*
 * 07_factorial.c - Iterative factorial
 * Tests: Loop, multiplication, comparison
 */

int factorial(int n) {
    int result = 1;
    int i = 1;
    while (i <= n) {
        result = result * i;
        i = i + 1;
    }
    return result;
}

int main(void) {
    return factorial(5);  /* 120 */
}
