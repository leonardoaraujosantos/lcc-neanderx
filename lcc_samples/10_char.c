/*
 * 10_char.c - Character (8-bit) operations
 * Tests: 8-bit char type, promotion to int
 */

char to_upper(char c) {
    if (c >= 'a' && c <= 'z') {
        return c - 32;
    }
    return c;
}

int main(void) {
    char a = 'h';
    char b = 'i';
    char A = to_upper(a);
    char B = to_upper(b);
    return A + B;  /* 'H' + 'I' = 72 + 73 = 145 */
}
