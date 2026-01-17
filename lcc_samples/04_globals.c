/*
 * 04_globals.c - Global variable test
 * Tests: Global variable declaration, access, modification
 */

int counter;
int step;

int increment(void) {
    counter = counter + step;
    return counter;
}

int main(void) {
    counter = 0;
    step = 5;
    increment();    /* counter = 5 */
    increment();    /* counter = 10 */
    increment();    /* counter = 15 */
    return counter;
}
