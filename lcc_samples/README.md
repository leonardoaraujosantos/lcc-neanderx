# LCC NEANDER-X 16-bit Sample Programs

This folder contains sample C programs that demonstrate the 16-bit NEANDER-X LCC compiler backend.

## Type Sizes (16-bit Architecture)

| Type | Size | Notes |
|------|------|-------|
| char | 1 byte | 8-bit character |
| short | 2 bytes | 16-bit native |
| int | 2 bytes | 16-bit native |
| long | 4 bytes | 32-bit extended |
| pointer | 2 bytes | 16-bit address space |

## Sample Programs

| File | Description | Tests |
|------|-------------|-------|
| 01_hello.c | Simple return | Basic function, 16-bit constant |
| 02_locals.c | Local variables | Stack allocation, 16-bit values |
| 03_arithmetic.c | Arithmetic | 16-bit add/sub with ADC/SBC |
| 04_globals.c | Global variables | BSS allocation, global access |
| 05_loop.c | Loop construct | While loop, 16-bit comparison |
| 06_array.c | Arrays | Global array, indexed access |
| 07_factorial.c | Factorial | Loop, 16-bit multiplication |
| 08_fibonacci.c | Fibonacci | Recursion, function calls |
| 09_bitwise.c | Bitwise ops | 16-bit AND, OR, XOR |
| 10_char.c | Char operations | 8-bit type, promotion to int |

## Compiling

```bash
# Compile a single file
./build/rcc -target=neanderx lcc_samples/01_hello.c > output.s

# Compile all samples
for f in lcc_samples/*.c; do
    base=$(basename "$f" .c)
    ./build/rcc -target=neanderx "$f" > "lcc_samples/${base}.s"
done
```

## Assembly Output

Each `.c` file has a corresponding `.s` assembly file showing the generated NEANDER-X 16-bit code.

Key assembly features:
- 16-bit values use lo/hi byte pairs
- ADC/SBC for multi-byte arithmetic
- Y:AC pair for 16-bit return values
- Frame-relative addressing (FP+offset) for locals/params
