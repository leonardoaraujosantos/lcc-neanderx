/*
 * 08_fibonacci.c - Fibonacci sequence
 * Tests: Recursion, multiple function calls, comparison
 */

int fib(int n) {
    if (n <= 1) {
        return n;
    }
    return fib(n - 1) + fib(n - 2);
}

int main(void) {
    return fib(10);  /* 55 */
}
