# NEANDER-X LCC Backend

This directory contains the LCC compiler backend for the NEANDER-X 8-bit educational processor.

## Overview

The NEANDER-X is an 8-bit accumulator-based processor designed for educational purposes. This LCC backend generates assembly code that can be assembled and run on a NEANDER-X simulator or hardware.

## Type Sizes

| Type | Size | Notes |
|------|------|-------|
| char | 1 byte | Native size |
| short | 1 byte | Limited to 8-bit |
| int | 1 byte | Native size |
| long | 2 bytes | Uses ADC/SBC |
| pointer | 2 bytes | 16-bit address space |
| float | N/A | Not supported |
| double | N/A | Not supported |

## Register Usage

| Register | Usage |
|----------|-------|
| AC | Accumulator - primary computation register |
| X | Index register - array indexing, MUL operand |
| Y | Index register - MUL high byte result, second index |
| FP | Frame pointer - local variable access (16-bit) |
| SP | Stack pointer - implicit management (16-bit) |
| PC | Program counter (16-bit) |

## Calling Convention

- Arguments are pushed right-to-left on the stack
- 8-bit return values are in AC
- 16-bit return values: low byte in AC, high byte in Y
- Caller cleans up arguments
- FP-relative addressing for parameters and locals

### Stack Frame Layout

```
High addresses
+----------------+
| Argument N     | [FP + N+3]
| ...            |
| Argument 1     | [FP + 4]
+----------------+
| Return Addr Hi | [FP + 3]
| Return Addr Lo | [FP + 2]
+----------------+
| Saved FP Hi    | [FP + 1]
| Saved FP Lo    | [FP + 0] <- FP points here
+----------------+
| Local 1        | [FP - 1]
| Local 2        | [FP - 2]
| ...            |
+----------------+ <- SP
Low addresses
```

## Building

```bash
# Build lburg first
cd lburg
make

# Build the compiler with NEANDER-X backend
cd ..
make BUILDDIR=build TARGET=neanderx HOSTFILE=etc/neanderx.c

# Or manually:
./build/lburg src/neanderx.md > build/neanderx.c
cc -c -Isrc -o build/neanderx.o build/neanderx.c
```

## Usage

```bash
# Compile to assembly
./build/rcc -target=neanderx test.c > test.s

# Or with the driver:
./build/lcc -Wf-target=neanderx -S test.c
```

## Test Programs

See the `tst/` directory for example programs:

- `test_basic.c` - Basic arithmetic and function calls
- `test_control.c` - Control flow (if/else, while, recursion)
- `test_array.c` - Arrays and multiplication/division

## Assembly Output Format

The generated assembly uses NEANDER-X mnemonics:

```asm
; Function: main
_main:
    ; Prologue
    PUSH_FP         ; Save caller's FP
    TSF             ; FP = SP

    ; Function body
    LDI 5           ; AC = 5
    PUSH            ; Save to stack
    ...

    ; Epilogue
    TFS             ; SP = FP
    POP_FP          ; Restore FP
    RET             ; Return
```

## Limitations

1. **No floating-point support** - The NEANDER-X has no FPU
2. **8-bit native operations** - 16/32-bit ops require multiple instructions
3. **Single accumulator** - Complex expressions need temp storage
4. **No indirect addressing** - Only indexed with X, Y, FP
5. **Limited registers** - Heavy use of stack for intermediates

## See Also

- [NEANDER-X CPU Documentation](../../README.md)
- [LCC Backend Guide](../../docs/LCC_NEANDER_BACKEND.md)
- [LCC Compiler Reference](../../docs/LCC_COMPILER_COMPLETE.md)
