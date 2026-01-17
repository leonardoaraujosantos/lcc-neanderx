/*
 * 06_array.c - Array test
 * Tests: Global array, indexed access, 16-bit elements
 */

int data[5];

int sum_array(void) {
    int sum = 0;
    sum = sum + data[0];
    sum = sum + data[1];
    sum = sum + data[2];
    sum = sum + data[3];
    sum = sum + data[4];
    return sum;
}

int main(void) {
    data[0] = 10;
    data[1] = 20;
    data[2] = 30;
    data[3] = 40;
    data[4] = 50;
    return sum_array();  /* 150 */
}
