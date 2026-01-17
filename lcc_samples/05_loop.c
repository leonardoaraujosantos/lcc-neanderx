/*
 * 05_loop.c - Loop and comparison test
 * Tests: While loop, 16-bit comparison, increment
 */

int sum_to_n(int n) {
    int sum = 0;
    int i = 1;
    while (i <= n) {
        sum = sum + i;
        i = i + 1;
    }
    return sum;
}

int main(void) {
    return sum_to_n(10);  /* 1+2+...+10 = 55 */
}
