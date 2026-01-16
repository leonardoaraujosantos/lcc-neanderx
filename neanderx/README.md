# NEANDER-X LCC Backend v4.0 (16-bit)

This directory contains the LCC compiler backend for the NEANDER-X 16-bit educational processor.

## Overview

The NEANDER-X is a 16-bit processor designed for educational purposes. This LCC backend generates optimized assembly code using the full LCC Extension Instruction Set. The 16-bit version provides native 16-bit `int` type and 32-bit `long` type for extended arithmetic.

## Version 3.0 Features

This version uses the complete LCC Extension instructions for optimal code generation:

| Instruction | Old Approach | New Approach | Improvement |
|-------------|--------------|--------------|-------------|
| Add reg+reg | TAX, POP, STA _tmp, TXA, ADD _tmp | TAX, POP, ADDX | 40% fewer cycles |
| Sub reg-reg | 6 instructions + 2 memory ops | SWPX, POP, SUBX | 66% fewer cycles |
| AND/OR/XOR reg | 4 instructions + memory | TAX, POP, ANDX/ORX/XORX | 50% fewer cycles |
| Compare imm | LDI, STA _tmp, LDA, CMP _tmp | CMPI imm | 75% fewer cycles |
| Multiply imm | LDXI imm, MUL | MULI imm | Single instruction |
| Divide imm | LDXI imm, DIV | DIVI imm | Single instruction |
| Pointer deref | Complex multi-step | LDA (addr) | Single instruction |
| Indexed indirect | Complex multi-step | LDA (addr),Y | 2 instructions |
| Shift loop counter | TXA, DEC, TAX | DEX | 66% fewer cycles |

## Type Sizes (16-bit Architecture)

| Type | Size | Alignment | Notes |
|------|------|-----------|-------|
| char | 1 byte | 1-byte | 8-bit character |
| short | 2 bytes | 2-byte | 16-bit native |
| int | 2 bytes | 2-byte | 16-bit native word |
| long | 4 bytes | 2-byte | 32-bit extended (uses ADC/SBC) |
| pointer | 2 bytes | 2-byte | 16-bit address space |
| float | N/A | N/A | Not supported |
| double | N/A | N/A | Not supported |

## Register Usage

| Register | Usage |
|----------|-------|
| AC | Accumulator - primary computation register |
| X | Index register - array indexing, MUL/DIV operand |
| Y | Index register - MUL high byte, DIV remainder, second index |
| FP | Frame pointer - local variable access (16-bit) |
| SP | Stack pointer - implicit management (16-bit) |
| PC | Program counter (16-bit) |

## Instructions Used by the Backend

### Register-to-Register ALU (No Memory Traffic)
- `ADDX` - AC = AC + X
- `SUBX` - AC = AC - X
- `ANDX` - AC = AC & X
- `ORX` - AC = AC | X
- `XORX` - AC = AC ^ X

### Immediate Operations
- `CMPI imm` - Compare AC with immediate (sets flags)
- `MULI imm` - AC = AC * imm (Y gets high byte)
- `DIVI imm` - AC = AC / imm (Y gets remainder)

### Indirect Addressing (Pointer Operations)
- `LDA (addr)` - Load from address stored at addr (*ptr)
- `STA (addr)` - Store to address stored at addr (*ptr = val)
- `LDA (addr),Y` - Indirect indexed (ptr[i])

### Register Operations
- `SWPX` - Swap AC and X (for operand reordering)
- `SWPY` - Swap AC and Y
- `DEX` - Decrement X (for loop counters)
- `DEY` - Decrement Y

### Standard Instructions
All original NEANDER-X instructions including:
- Memory: LDA, STA, LDA addr,X, LDA addr,Y, LDA addr,FP
- Arithmetic: ADD, SUB, ADC, SBC, MUL, DIV, MOD, INC, DEC, NEG
- Bitwise: AND, OR, XOR, NOT, SHL, SHR, ASR
- Compare: CMP
- Jumps: JMP, JZ, JNZ, JN, JC, JNC, JLE, JGT, JGE, JBE, JA
- Stack: PUSH, POP, PUSH_FP, POP_FP, TSF, TFS
- Calls: CALL, RET

## Calling Convention (16-bit)

- Arguments pushed right-to-left on stack (2-byte aligned)
- 8-bit return values in AC
- 16-bit return values: low byte in AC, high byte in Y (Y:AC)
- 32-bit return values: pushed to stack or Y:AC pairs
- Caller cleans up arguments
- FP-relative addressing for parameters and locals

### Stack Frame Layout (16-bit aligned)

```
High addresses
+------------------+
| Parameter N      | [FP + 4 + 2*(N-1)]   <- Last parameter
| ...              |
| Parameter 1      | [FP + 4]             <- First parameter
+------------------+
| Return Addr Hi   | [FP + 3]             <- 16-bit return address
| Return Addr Lo   | [FP + 2]
+------------------+
| Saved FP Hi      | [FP + 1]             <- 16-bit saved FP
| Saved FP Lo      | [FP + 0]             <- FP points here
+------------------+
| Local 1 (hi)     | [FP - 1]             <- 16-bit local variables
| Local 1 (lo)     | [FP - 2]
| Local 2 (hi)     | [FP - 3]
| Local 2 (lo)     | [FP - 4]
| ...              |
+------------------+ <- SP
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

The generated assembly uses NEANDER-X mnemonics with v4.0 16-bit optimizations:

```asm
; NEANDER-X 16-bit Assembly
; Generated by LCC v4.0 (16-bit target)
; Uses: ADC/SBC for 16-bit ops, ADDX/SUBX for reg-to-reg

; Function: add_values (16-bit parameters)
_add_values:
    ; Prologue
    PUSH_FP         ; Save caller's FP
    TSF             ; FP = SP

    ; 16-bit addition: a + b (parameters are 2 bytes each)
    LDA 4,FP        ; Load parameter a (low byte)
    PUSH
    LDA 5,FP        ; Load parameter a (high byte)
    STA _tmp_hi
    POP
    STA _tmp_lo
    LDA 6,FP        ; Load parameter b (low byte)
    ADD _tmp_lo     ; Add low bytes
    PUSH
    LDA 7,FP        ; Load parameter b (high byte)
    ADC _tmp_hi     ; Add high bytes with carry
    ; Result in Y:AC (high:low)

    ; Epilogue
    TFS             ; SP = FP
    POP_FP          ; Restore FP
    RET             ; Return
```

## Code Size (16-bit operations)

Typical instruction counts for 16-bit operations:

| Operation | 8-bit CPU | 16-bit CPU | Notes |
|-----------|-----------|------------|-------|
| int + int | N/A | 10-12 instr | Uses ADC for carry |
| int - int | N/A | 12-15 instr | Uses SBC for borrow |
| long + long | N/A | 20-25 instr | 4-byte with carry chain |
| char + char | 3 instr | 3 instr | Same as before |
| *ptr (16-bit) | 2 instr | 4 instr | Load 2 bytes |

## Limitations

1. **No floating-point support** - The NEANDER-X has no FPU
2. **8-bit data registers** - AC, X, Y are 8-bit; 16/32-bit ops require multi-byte sequences
3. **Single accumulator** - Complex expressions may need temp storage
4. **Limited indirect function calls** - Only direct CALL addr supported
5. **32-bit operations slow** - long arithmetic requires 4-byte carry/borrow chains

## See Also

- [NEANDER-X CPU Documentation](../../README.md)
- [LCC Backend Guide](../../docs/LCC_NEANDER_BACKEND.md)
- [LCC Compiler Reference](../../docs/LCC_COMPILER_COMPLETE.md)
