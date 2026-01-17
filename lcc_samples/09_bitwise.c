/*
 * 09_bitwise.c - Bitwise operations test
 * Tests: AND, OR, XOR on 16-bit values
 */

int and_op(int a, int b) {
    return a & b;
}

int or_op(int a, int b) {
    return a | b;
}

int xor_op(int a, int b) {
    return a ^ b;
}

int main(void) {
    int a = 255;     /* 0x00FF */
    int b = 3855;    /* 0x0F0F */
    int r1 = and_op(a, b);
    int r2 = or_op(a, b);
    int r3 = xor_op(a, b);
    return r1 + r2 + r3;
}
