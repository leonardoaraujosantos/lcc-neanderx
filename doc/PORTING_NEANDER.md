# Porting LCC to the NEANDER-X Processor: A Complete Tutorial

This document provides a comprehensive, step-by-step guide to porting the LCC (Little C Compiler) to the NEANDER-X 16-bit educational processor. Whether you're a student learning about compilers or a hobbyist building your own CPU, this tutorial will walk you through the entire process.

**Note:** This guide has been updated for the 16-bit version of NEANDER-X where `int` is 2 bytes (16-bit native) and `long` is 4 bytes (32-bit).

## Table of Contents

1. [Introduction](#introduction)
2. [Prerequisites](#prerequisites)
3. [Understanding the NEANDER-X Architecture](#understanding-the-neander-x-architecture)
4. [LCC Backend Architecture Overview](#lcc-backend-architecture-overview)
5. [Step 1: Setting Up the Build System](#step-1-setting-up-the-build-system)
6. [Step 2: Creating the Machine Description File](#step-2-creating-the-machine-description-file)
7. [Step 3: Understanding Terminal Definitions](#step-3-understanding-terminal-definitions)
8. [Step 4: Writing Grammar Rules](#step-4-writing-grammar-rules)
9. [Step 5: Implementing Interface Functions](#step-5-implementing-interface-functions)
10. [Step 6: Register Management](#step-6-register-management)
11. [Step 7: Calling Conventions](#step-7-calling-conventions)
12. [Step 8: Compiling and Using the NEANDER-X Backend](#step-8-compiling-and-using-the-neander-x-backend)
13. [Step 9: Testing Your Backend](#step-9-testing-your-backend)
14. [Tips and Tricks](#tips-and-tricks)
15. [Common Pitfalls and Solutions](#common-pitfalls-and-solutions)
16. [References](#references)

---

## Introduction

LCC is a retargetable ANSI C compiler originally developed by Chris Fraser and David Hanson. "Retargetable" means you can adapt it to generate code for different processor architectures by writing a new backend. This tutorial documents the process of creating a backend for the NEANDER-X, a 16-bit educational processor with 8-bit data registers and 16-bit address space.

### Why Port LCC?

- **Educational Value**: Understanding how compilers work at a deep level
- **Practical Application**: Enable C programming for custom/hobby CPUs
- **Relatively Simple**: LCC backends are typically 400-600 lines of code
- **Well Documented**: Extensive documentation and examples available

### What You'll Learn

- How LCC's instruction selection works using tree pattern matching
- How to define terminal symbols for your target architecture
- How to write grammar rules that generate assembly code
- How to implement the required interface functions
- How to handle the challenges of a limited 8-bit architecture

---

## Prerequisites

Before starting, ensure you have:

1. **LCC Source Code**: Clone from https://github.com/drh/lcc
2. **C Compiler**: GCC or Clang to build LCC itself
3. **Basic Knowledge**:
   - C programming
   - Assembly language concepts
   - Your target processor's instruction set
4. **Tools**: make, ar, and standard Unix utilities

### Getting LCC

```bash
git clone https://github.com/drh/lcc.git
cd lcc
```

---

## Understanding the NEANDER-X Architecture

The NEANDER-X is an 8-bit educational processor designed with C compiler support in mind. It extends the original NEANDER with features specifically chosen to enable efficient C code generation.

### Registers

| Register | Size | Description |
|----------|------|-------------|
| AC | 8-bit | Accumulator - main computation register |
| X | 8-bit | Index register - array access, expression temporary |
| Y | 8-bit | Index register - MUL high byte, DIV remainder, expression temporary |
| PC | 16-bit | Program counter |
| SP | 16-bit | Stack pointer (grows downward) |
| FP | 16-bit | Frame pointer - essential for C stack frames |

### Condition Flags

- **N** (Negative): Set when result is negative (sign bit = 1)
- **Z** (Zero): Set when result is zero
- **C** (Carry): Set on carry/borrow - used for multi-byte arithmetic and unsigned comparisons

### Key Instructions

```assembly
; Memory Access
LDA addr        ; Load AC from memory
STA addr        ; Store AC to memory
LDI imm         ; Load immediate to AC

; Indexed Addressing (critical for arrays and stack frames)
LDA addr,X      ; Load AC from memory[addr + X]
STA addr,X      ; Store AC to memory[addr + X]
LDA addr,Y      ; Load AC from memory[addr + Y]
STA addr,Y      ; Store AC to memory[addr + Y]
LDA addr,FP     ; Load AC from memory[addr + FP] - local variables!
STA addr,FP     ; Store AC to memory[addr + FP] - local variables!

; Register Transfers
TAX / TXA       ; Transfer AC <-> X
TAY / TYA       ; Transfer AC <-> Y
LDXI imm        ; Load immediate to X
LDYI imm        ; Load immediate to Y
INX / INY       ; Increment X / Y

; Arithmetic with Carry (for multi-byte operations)
ADD addr        ; AC = AC + mem[addr]
SUB addr        ; AC = AC - mem[addr]
ADC addr        ; AC = AC + mem[addr] + Carry
SBC addr        ; AC = AC - mem[addr] - Carry
INC / DEC       ; Increment / Decrement AC
NEG             ; AC = -AC (two's complement)

; Hardware Multiply/Divide
MUL             ; Y:AC = AC * X (16-bit result!)
DIV             ; AC = AC / X (quotient), Y = remainder
MOD             ; AC = AC % X (remainder), Y = quotient

; Bitwise Operations
AND/OR/XOR addr ; Bitwise with memory
NOT             ; AC = ~AC
SHL / SHR / ASR ; Shift left / logical right / arithmetic right

; Comparison
CMP addr        ; Compare AC with memory (sets N, Z, C flags)

; Jumps (using NEANDER-X extended jump set)
JMP addr        ; Unconditional jump
JZ / JNZ addr   ; Jump if Zero / Not Zero
JN addr         ; Jump if Negative
JC / JNC addr   ; Jump if Carry / No Carry (unsigned comparisons)
JLE / JGT addr  ; Jump if Less/Equal or Greater (signed)
JGE addr        ; Jump if Greater or Equal (signed)
JBE / JA addr   ; Jump if Below/Equal or Above (unsigned)

; Stack and Subroutines
PUSH / POP      ; Push/Pop AC to/from stack
PUSH_FP / POP_FP; Push/Pop Frame Pointer
TSF / TFS       ; Transfer SP to FP / FP to SP
CALL addr       ; Call subroutine (pushes 16-bit return address)
RET             ; Return from subroutine
```

### LCC Extension Instructions (v3.0)

These instructions were added specifically to optimize C compiler code generation:

```assembly
; Register-to-Register ALU (eliminates memory traffic)
ADDX            ; AC = AC + X
SUBX            ; AC = AC - X
ADDY            ; AC = AC + Y
SUBY            ; AC = AC - Y
ANDX            ; AC = AC & X
ORX             ; AC = AC | X
XORX            ; AC = AC ^ X

; Immediate Operations
CMPI imm        ; Compare AC with immediate (sets flags, preserves AC)
MULI imm        ; AC = AC * imm; Y = high byte of result
DIVI imm        ; AC = AC / imm; Y = remainder

; Indirect Addressing (pointer operations)
LDA (addr)      ; AC = MEM[MEM[addr]] - dereference pointer
STA (addr)      ; MEM[MEM[addr]] = AC - store through pointer
LDA (addr),Y    ; AC = MEM[MEM[addr] + Y] - indexed through pointer

; Swap Operations (operand reordering)
SWPX            ; Swap AC and X
SWPY            ; Swap AC and Y

; Decrement X/Y (loop optimization)
DEX             ; X = X - 1
DEY             ; Y = Y - 1

; Loop Primitive
DECJNZ addr     ; AC = AC - 1; if AC != 0: jump to addr
```

**Why These Instructions Matter for C:**

| Instruction | C Pattern | Benefit |
|-------------|-----------|---------|
| ADDX/SUBX | `a + b` | No memory temp needed |
| CMPI | `if (x == 5)` | Direct constant comparison |
| MULI/DIVI | `x * 10`, `x / 3` | Single instruction for constant ops |
| LDA (addr) | `*ptr` | Direct pointer dereference |
| LDA (addr),Y | `ptr[i]` | Array through pointer in 2 instructions |
| DEX/DEY | `for` loops | Efficient loop counters |
| SWPX | `b - a` | Operand reordering without temps |

### Memory Model (16-bit Architecture)

- 16-bit address space (64KB via SPI SRAM)
- 8-bit data bus (16-bit values require 2 memory accesses)
- Stack grows downward (SP decrements on push)
- Little-endian byte order
- Stack pointer starts at 0x00FF, grows toward 0x0000
- Code/data starts at 0x0100
- Native word size: 16-bit (int = 2 bytes)

### Why NEANDER-X is Good for C Compilation

Unlike the original NEANDER (which only had AC), NEANDER-X was specifically extended for C:

1. **Frame Pointer (FP)**: Enables standard C calling conventions with local variables at fixed offsets from FP
2. **Indexed Addressing**: `LDA addr,FP` provides efficient access to function parameters and locals
3. **X and Y Registers**: Serve as expression temporaries, reducing memory traffic
4. **Hardware MUL/DIV**: No need for slow software multiplication routines
5. **ADC/SBC**: Enable multi-byte (16-bit, 32-bit) arithmetic with carry propagation
6. **Rich Comparison Jumps**: Full set of signed and unsigned conditional branches
7. **CMP Instruction**: Sets all flags without modifying AC, enabling efficient comparisons

**LCC Extension Additions (v3.0):**

8. **Register-to-Register ALU**: ADDX/SUBX/ANDX/ORX/XORX eliminate memory temps for binary operations
9. **Immediate Operations**: CMPI/MULI/DIVI for direct constant operations
10. **Indirect Addressing**: LDA (addr) and LDA (addr),Y for efficient pointer operations
11. **Swap Instructions**: SWPX/SWPY for operand reordering without temporaries
12. **DEX/DEY**: Direct decrement for loop counters

### Remaining Challenges (16-bit Architecture)

1. **8-bit Data Registers**: AC, X, Y are 8-bit; 16-bit operations require multi-byte sequences
2. **Complex Expressions**: While much improved with reg-to-reg ops, some expressions still need temps
3. **32-bit Operations**: long arithmetic requires 4-byte carry/borrow chains
4. **Memory Overhead**: Each 16-bit memory access requires 2 SPI transactions

---

## LCC Backend Architecture Overview

An LCC backend consists of three main components:

### 1. Machine Description File (`.md`)

This is the heart of your backend. It contains:
- **Prologue**: C code with declarations and helper functions
- **Terminal Definitions**: LCC IR operations your backend handles
- **Grammar Rules**: Pattern matching rules that emit assembly
- **Epilogue**: Implementation of interface functions

### 2. Driver Configuration (`etc/target.c`)

Configures how the `lcc` driver invokes:
- Preprocessor (cpp)
- Compiler (rcc)
- Assembler
- Linker

### 3. Build System Integration

Modifications to:
- `src/bind.c`: Register your backend
- `makefile`: Build rules for your target

### How Instruction Selection Works

LCC uses a technique called **BURS** (Bottom-Up Rewrite System):

1. The front-end generates an intermediate representation (IR) as a tree
2. The IR tree is "labeled" by matching patterns from your grammar
3. The pattern with the lowest "cost" is selected
4. The corresponding code template is emitted

```
C Code:        x = a + b;
                   ↓
IR Tree:       ASGNI(ADDRLP x, ADDI(INDIRI(ADDRLP a), INDIRI(ADDRLP b)))
                   ↓
Pattern Match: stmt: ASGNI(addr, reg)  "STA %0\n"
               reg:  ADDI(reg, reg)    "ADD ...\n"
               reg:  INDIRI(addr)      "LDA %0\n"
               addr: ADDRLP            "%a"
                   ↓
Assembly:      LDA a
               ADD b
               STA x
```

---

## Step 1: Setting Up the Build System

### 1.1 Edit `src/bind.c`

Add your target to the binding list:

```c
#define yy \
xx(alpha/osf,    alphaIR) \
xx(mips/irix,    mipsebIR) \
xx(sparc/sun,    sparcIR) \
xx(x86/linux,    x86linuxIR) \
xx(neanderx,     neanderxIR) \    /* ADD THIS LINE */
xx(symbolic,     symbolicIR) \
xx(null,         nullIR)
```

This registers your backend with the name `neanderx` and Interface struct `neanderxIR`.

### 1.2 Edit `makefile`

Add build rules for your backend:

```makefile
# Add to RCCOBJS
RCCOBJS=$Balloc$O ... $Bneanderx$O

# Add lburg rule
$Bneanderx.c: $Blburg$E src/neanderx.md
	$Blburg src/neanderx.md $@

# Add compilation rule
$Bneanderx$O: $Bneanderx.c
	$(CC) $(CFLAGS) -c -Isrc -o $@ $Bneanderx.c
```

### 1.3 Create `custom.mk` (Optional)

For convenience:

```makefile
BUILDDIR=build
TARGET=neanderx
HOSTFILE=etc/neanderx.c
```

### 1.4 Create `etc/neanderx.c`

The driver configuration file:

```c
/* NEANDER-X LCC driver configuration */

#include <string.h>

char *suffixes[] = { ".c", ".i", ".s", ".o", ".out", 0 };

char inputs[256] = "";

char *cpp[] = {
    "/usr/bin/cpp",
    "-D__NEANDERX__",
    "$1", "$2", "$3", 0
};

char *com[] = {
    "$BUILDDIR/rcc",
    "-target=neanderx",
    "$1", "$2", "$3", 0
};

char *include[] = { "-I" LCCDIR "/neanderx/include", 0 };

char *as[] = { "/usr/bin/as", "-o", "$3", "$1", "$2", 0 };

char *ld[] = { "/usr/bin/ld", "-o", "$3", "$1", "$2", 0 };

int option(char *arg) {
    if (strcmp(arg, "-g") == 0) { /* debug flag */ }
    return 0;
}
```

---

## Step 2: Creating the Machine Description File

Create `src/neanderx.md`. The file has this structure:

```
%{
/* PROLOGUE: C code */
#include "c.h"

/* Declarations and helper functions */
%}

%start stmt

/* TERMINAL DEFINITIONS */
%term CNSTI1=1045
...

%%

/* GRAMMAR RULES */
reg: CNSTI1  "LDI %a\n"  1
...

%%

/* EPILOGUE: Interface function implementations */
static void progbeg(int argc, char *argv[]) { ... }
...

Interface neanderxIR = { ... };
```

### The Prologue Section

```c
%{
#include "c.h"

/* Required macros for lburg */
#define NODEPTR_TYPE Node
#define OP_LABEL(p) ((p)->op)
#define LEFT_CHILD(p) ((p)->kids[0])
#define RIGHT_CHILD(p) ((p)->kids[1])
#define STATE_LABEL(p) ((p)->x.state)

/* Register definitions */
enum { REG_AC=0, REG_X=1, REG_Y=2 };
#define IREG 1    /* Integer register class */

/* Global variables */
static Symbol intreg[32];   /* Register array */
static Symbol intregw;      /* Register wildcard */
static int cseg;            /* Current segment */

/* Helper function declarations */
static void address(Symbol, Symbol, long);
static void defconst(int, int, Value);
/* ... more declarations ... */

/* Helper macro for constant ranges */
#define range(p, lo, hi) \
    ((p)->syms[0]->u.c.v.i >= (lo) && \
     (p)->syms[0]->u.c.v.i <= (hi) ? 0 : LBURG_MAX)

%}
```

---

## Step 3: Understanding Terminal Definitions

Terminals represent LCC's intermediate representation (IR) operations. Each terminal has a unique numeric code calculated as:

```
terminal = size * 1024 + op * 16 + type + 5
```

Where:
- `size`: 1, 2, 4, or 8 bytes
- `op`: Operation number (from `src/ops.h`)
- `type`: I=0, U=1, P=2 (Integer, Unsigned, Pointer)

### Common Operations (from ops.h)

| Operation | Number | Description |
|-----------|--------|-------------|
| CNST | 1 | Constant |
| ARG | 2 | Function argument |
| ASGN | 3 | Assignment |
| INDIR | 4 | Indirection (dereference) |
| NEG | 12 | Negation |
| CALL | 13 | Function call |
| LOAD | 14 | Register load |
| RET | 15 | Return |
| ADDRG | 16 | Address of global |
| ADDRF | 17 | Address of parameter |
| ADDRL | 18 | Address of local |
| ADD | 19 | Addition |
| SUB | 20 | Subtraction |
| MUL | 29 | Multiplication |
| DIV | 28 | Division |
| EQ | 30 | Equal comparison |
| NE | 35 | Not equal |
| LT | 34 | Less than |
| GT | 32 | Greater than |
| JUMP | 36 | Unconditional jump |
| LABEL | 37 | Label definition |

### Calculating Terminal Numbers

Example: ADDI1 (Add Integer, 1 byte)
- size = 1: 1 * 1024 = 1024
- op = ADD = 19: 19 * 16 = 304
- type = I = 0
- Add 5: +5
- Total: 1024 + 304 + 0 + 5 = **1333**

### Terminal Definitions for NEANDER-X

```
%start stmt

/* Constants */
%term CNSTI1=1045
%term CNSTU1=1046
%term CNSTI2=2069
%term CNSTU2=2070
%term CNSTP2=2071
%term CNSTI4=4117
%term CNSTU4=4118

/* Arguments */
%term ARGB=41
%term ARGI1=1061
%term ARGU1=1062
%term ARGI4=4133

/* Assignments */
%term ASGNB=57
%term ASGNI1=1077
%term ASGNU1=1078
%term ASGNI4=4149

/* Indirection (loads from memory) */
%term INDIRB=73
%term INDIRI1=1093
%term INDIRU1=1094
%term INDIRI4=4165

/* Address operations */
%term ADDRGP2=2311
%term ADDRFP2=2327
%term ADDRLP2=2343
%term ADDRGP4=4359
%term ADDRFP4=4375
%term ADDRLP4=4391

/* Arithmetic */
%term ADDI1=1333
%term ADDU1=1334
%term ADDI4=4405
%term SUBI1=1349
%term SUBU1=1350
%term MULI1=1493
%term DIVI1=1477

/* Conversions */
%term CVII1=1157
%term CVII4=4229
%term CVIU1=1158
%term CVUI1=1205

/* Comparisons */
%term EQI1=1509
%term NEI1=1589
%term LTI1=1573
%term GTI1=1541

/* Control flow */
%term JUMPV=584
%term LABELV=600

/* Function calls and returns */
%term CALLV=216
%term CALLI1=1237
%term CALLI4=4309
%term RETV=248
%term RETI1=1269
%term RETI4=4341

/* Register loads */
%term LOADI1=1253
%term LOADU1=1254
%term LOADI4=4325

/* Virtual register */
%term VREGP=711
```

### Important Note on 4-Byte Operations

Even for an 8-bit processor, you need to handle 4-byte operations because C promotes `char` and `short` to `int` for arithmetic and function returns. Your rules can truncate these to 8-bit since that's what the result actually needs.

---

## Step 4: Writing Grammar Rules

Grammar rules define how IR patterns translate to assembly code.

### Rule Syntax

```
nonterminal: pattern  "template"  cost
```

- **nonterminal**: Target of this rule (stmt, reg, addr, etc.)
- **pattern**: IR tree pattern to match
- **template**: Assembly code to emit (with substitution markers)
- **cost**: Relative cost for instruction selection

### Template Substitution Markers

| Marker | Meaning |
|--------|---------|
| `%a` | Symbol name from node |
| `%0` | First child's result |
| `%1` | Second child's result |
| `%c` | Register name |
| `%%` | Literal percent sign |

### Nonterminals for NEANDER-X

```
stmt   - Statement (root of expression tree)
reg    - Value in accumulator
addr   - Memory address
con1   - 1-byte constant
con4   - 4-byte constant
conN   - Constant equal to 1
```

### Basic Rules

```
%%

/* Virtual register access (required by LCC) */
reg: INDIRI1(VREGP)    "# read vreg\n"
reg: INDIRU1(VREGP)    "# read vreg\n"
reg: INDIRI4(VREGP)    "# read vreg\n"

stmt: ASGNI1(VREGP,reg)  "# write vreg\n"
stmt: ASGNU1(VREGP,reg)  "# write vreg\n"
stmt: ASGNI4(VREGP,reg)  "# write vreg\n"

/* Constants */
con1: CNSTI1  "%a"
con1: CNSTU1  "%a"

con4: CNSTI4  "%a"
con4: CNSTU4  "%a"

/* Load constant into accumulator */
reg: con1  "    LDI %0\n"  1
reg: con4  "    LDI %0\n"  1

/* Address nonterminals */
addr: ADDRGP2  "%a"      /* Global variable */
addr: ADDRFP2  "%a"      /* Function parameter */
addr: ADDRLP2  "%a"      /* Local variable */
addr: ADDRGP4  "%a"
addr: ADDRFP4  "%a"
addr: ADDRLP4  "%a"

/* Load from memory */
reg: INDIRI1(addr)  "    LDA %0\n"  2
reg: INDIRU1(addr)  "    LDA %0\n"  2
reg: INDIRI4(addr)  "    LDA %0\n"  2

/* Load from frame pointer offset (for parameters and locals)
 * Uses NEANDER-X indexed addressing: LDA offset,FP
 */
reg: INDIRI1(ADDRFP2)  "    LDA %a,FP\n"  2
reg: INDIRI1(ADDRLP2)  "    LDA %a,FP\n"  2

/* Store to memory */
stmt: ASGNI1(addr,reg)  "    STA %0\n"  2
stmt: ASGNU1(addr,reg)  "    STA %0\n"  2

/* Store to frame pointer offset */
stmt: ASGNI1(ADDRFP2,reg)  "    STA %a,FP\n"  2
stmt: ASGNI1(ADDRLP2,reg)  "    STA %a,FP\n"  2

/* Array access using X register: array[index]
 * Pattern matches: INDIR(ADD(base_addr, index_reg))
 */
reg: INDIRI1(ADDI2(addr,reg))  "    TAX\n    LDA %0,X\n"  3
stmt: ASGNI1(ADDI2(addr,reg),reg)  "    TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n"  5
```

### Arithmetic Rules

The key insight for NEANDER-X is using the X and Y registers as temporaries during binary operations. When LCC evaluates `a + b`, the left operand is pushed to the stack, then the right operand is computed into AC. Our rules save AC to X, pop the left operand, then perform the operation.

```
/* Addition: reg + reg
 * Right operand in AC, left on stack
 * Strategy: Save right to X temp, pop left, add from temp
 */
reg: ADDI1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    ADD _tmp\n"  4
reg: ADDU1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    ADD _tmp\n"  4

/* Addition with memory operand (most efficient - direct memory access) */
reg: ADDI1(reg,INDIRI1(addr))  "    ADD %1\n"  2

/* Increment (special case for +1 uses dedicated INC instruction) */
conN: CNSTI1  "%a"  range(a, 1, 1)
reg: ADDI1(reg,conN)  "    INC\n"  1

/* Subtraction needs care: left - right, but right is in AC */
reg: SUBI1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    STA _tmp2\n    LDA _tmp\n    SUB _tmp2\n"  6
reg: SUBI1(reg,INDIRI1(addr))  "    SUB %1\n"  2
reg: SUBI1(reg,conN)  "    DEC\n"  1

/* Multiplication: Uses hardware MUL instruction
 * MUL computes AC * X -> Y:AC (16-bit result)
 * Right operand goes to X, left to AC
 */
reg: MULI1(reg,reg)  "    TAX\n    POP\n    MUL\n"  3

/* Division and Modulo: Uses hardware DIV/MOD
 * DIV: AC / X -> AC (quotient), Y (remainder)
 * MOD: AC % X -> AC (remainder), Y (quotient)
 */
reg: DIVI1(reg,reg)  "    TAX\n    POP\n    DIV\n"  3
reg: MODI1(reg,reg)  "    TAX\n    POP\n    MOD\n"  3

/* Negation: Two's complement using dedicated NEG instruction */
reg: NEGI1(reg)  "    NEG\n"  1
```

### Bitwise Operations

```
reg: BANDI1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    AND _tmp\n"  5
reg: BORI1(reg,reg)   "    PUSH\n    STA _tmp\n    POP\n    OR _tmp\n"   5
reg: BXORI1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    XOR _tmp\n"  5
reg: BCOMI1(reg)      "    NOT\n"  1

/* Shifts */
reg: LSHI1(reg,conN)  "    SHL\n"  1
reg: RSHI1(reg,conN)  "    ASR\n"  1
reg: RSHU1(reg,conN)  "    SHR\n"  1
```

### Type Conversions

```
/* Truncation (4-byte to 1-byte) - just use low byte */
reg: CVII1(reg)  "# cvii1 - truncate\n"  0
reg: CVIU1(reg)  "# cviu1\n"  0
reg: CVUI1(reg)  "# cvui1\n"  0
reg: CVUU1(reg)  "# cvuu1\n"  0

/* Extension (1-byte to 4-byte) */
reg: CVII4(reg)  "# cvii4 - extend\n"  0
reg: CVIU4(reg)  "# cviu4\n"  0
reg: CVUI4(reg)  "# cvui4\n"  0
reg: CVUU4(reg)  "# cvuu4\n"  0
```

### Control Flow

NEANDER-X has a rich set of comparison jumps, making conditional code efficient:

```
/* Labels */
stmt: LABELV  "%a:\n"

/* Unconditional jump */
stmt: JUMPV(addr)  "    JMP %0\n"  1

/* Comparisons: CMP sets flags without modifying AC
 * After CMP, use the appropriate conditional jump:
 *   JZ/JNZ  - equal/not equal (tests Z flag)
 *   JN      - signed less than (tests N flag)
 *   JC/JNC  - unsigned less/greater-equal (tests C flag)
 *   JLE/JGT - signed less-equal/greater (tests N OR Z / N=0 AND Z=0)
 *   JGE     - signed greater-equal (tests N=0)
 *   JBE/JA  - unsigned below-equal/above (tests C OR Z / C=0 AND Z=0)
 */

/* Equal/Not Equal */
stmt: EQI1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JZ %a\n"  5
stmt: NEI1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JNZ %a\n"  5

/* Signed comparisons */
stmt: LTI1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JN %a\n"  5
stmt: LEI1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JLE %a\n"  5
stmt: GTI1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JGT %a\n"  5
stmt: GEI1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JGE %a\n"  5

/* Unsigned comparisons */
stmt: LTU1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JC %a\n"  5
stmt: LEU1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JBE %a\n"  5
stmt: GTU1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JA %a\n"  5
stmt: GEU1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JNC %a\n"  5

/* Optimized: comparison with memory operand (avoids temporary) */
stmt: EQI1(reg,INDIRI1(addr))  "    CMP %1\n    JZ %a\n"  3
stmt: NEI1(reg,INDIRI1(addr))  "    CMP %1\n    JNZ %a\n"  3
stmt: LTI1(reg,INDIRI1(addr))  "    CMP %1\n    JN %a\n"  3
```

### Function Calls and Returns

```
/* Push arguments */
stmt: ARGI1(reg)  "    PUSH\n"  1
stmt: ARGU1(reg)  "    PUSH\n"  1
stmt: ARGI4(reg)  "    PUSH\n"  1

/* Function calls */
reg: CALLI1(addr)  "    CALL %0\n"  5
reg: CALLI4(addr)  "    CALL %0\n"  5
stmt: CALLV(addr)  "    CALL %0\n"  5

/* Returns - result is already in AC */
stmt: RETI1(reg)  "# ret\n"  0
stmt: RETU1(reg)  "# ret\n"  0
stmt: RETI4(reg)  "# ret\n"  0
stmt: RETV        "# ret\n"  0

/* Register move (for register allocation) */
reg: LOADI1(reg)  ""  move(a)
reg: LOADU1(reg)  ""  move(a)
reg: LOADI4(reg)  ""  move(a)

/* Statement from any reg (discard value) */
stmt: reg  ""
```

### Important Rule Design Considerations

1. **Empty templates must be avoided** for "instruction" rules. Use a comment like `"# ret\n"` instead of `""` - empty templates cause instruction selection to fail.

2. **Cost values** guide instruction selection. Lower costs are preferred. Use higher costs for complex multi-instruction sequences.

3. **Order matters** for rules with the same cost. More specific patterns should come first.

4. **The `move(a)` cost function** is built into LCC and handles register-to-register moves.

---

## Step 5: Implementing Interface Functions

After the `%%` that ends the grammar rules, implement the interface functions.

### Program Beginning and End

```c
static void progbeg(int argc, char *argv[]) {
    int i;

    /* Parse command-line arguments */
    for (i = 1; i < argc; i++) {
        /* Handle -d for debug, etc. */
    }

    /* Initialize registers */
    intreg[REG_AC] = mkreg("AC", REG_AC, 1, IREG);
    intregw = mkwildcard(intreg);

    /* Set register masks */
    tmask[IREG] = 0x01;  /* Available registers */
    vmask[IREG] = 0;     /* Volatile registers (caller-saved) */

    /* Emit file header */
    print("; NEANDER-X Assembly\n");
    print("; Generated by LCC\n\n");

    /* Runtime variables */
    print("    .org 0x0000\n");
    print("_tmp:    .byte 0\n");
    print("_tmp_lo: .byte 0\n");
    print("_tmp_hi: .byte 0\n");
    print("\n    .org 0x0100\n\n");
}

static void progend(void) {
    print("\n; End of program\n");
    print("    HLT\n");
}
```

### Segment Management

```c
static void segment(int s) {
    if (cseg == s) return;
    cseg = s;
    switch (s) {
    case CODE: print("\n    .text\n"); break;
    case DATA: print("\n    .data\n"); break;
    case BSS:  print("\n    .bss\n");  break;
    case LIT:  print("\n    .rodata\n"); break;
    }
}
```

### Symbol Management

```c
static void defsymbol(Symbol p) {
    if (p->x.name == NULL) {
        if (p->scope >= LOCAL && p->sclass == STATIC)
            p->x.name = stringf("_L%d", genlabel(1));
        else if (p->generated)
            p->x.name = stringf("_L%s", p->name);
        else if (p->scope == GLOBAL || p->sclass == EXTERN)
            p->x.name = stringf("_%s", p->name);
        else
            p->x.name = p->name;
    }
}

static void address(Symbol q, Symbol p, long n) {
    if (p->scope == GLOBAL || p->sclass == STATIC || p->sclass == EXTERN)
        q->x.name = stringf("%s%s%D", p->x.name, n >= 0 ? "+" : "", n);
    else {
        q->x.offset = p->x.offset + n;
        q->x.name = stringf("%d", q->x.offset);
    }
}
```

### Data Definition

```c
static void defconst(int suffix, int size, Value v) {
    switch (size) {
    case 1: print("    .byte %d\n", v.u & 0xFF); break;
    case 2:
        print("    .byte %d\n", v.u & 0xFF);
        print("    .byte %d\n", (v.u >> 8) & 0xFF);
        break;
    }
}

static void defaddress(Symbol p) {
    print("    .word %s\n", p->x.name);
}

static void defstring(int len, char *s) {
    int i;
    for (i = 0; i < len; i++)
        print("    .byte %d\n", s[i] & 0xFF);
}

static void space(int n) {
    print("    .space %d\n", n);
}

static void export(Symbol p) {
    print("    .global %s\n", p->x.name);
}

static void import(Symbol p) {
    if (p->ref > 0)
        print("    .extern %s\n", p->x.name);
}

static void global(Symbol p) {
    print("%s:\n", p->x.name);
}
```

### Local Variables

```c
static void local(Symbol p) {
    offset = roundup(offset + p->type->size, p->type->align);
    p->x.offset = -offset;
    p->x.name = stringf("%d", -offset);
}
```

### Function Generation

NEANDER-X has dedicated instructions for stack frame management: `PUSH_FP`, `POP_FP`, `TSF` (Transfer SP to FP), and `TFS` (Transfer FP to SP). These enable standard C calling conventions:

```c
static void function(Symbol f, Symbol caller[], Symbol callee[], int ncalls) {
    int i;
    int param_offset;

    print("\n; Function: %s\n", f->name);
    print("%s:\n", f->x.name);

    /* Prologue - Standard C function entry
     * PUSH_FP: Save caller's frame pointer to stack
     * TSF:     Set FP = SP (establish new frame)
     */
    print("    ; Prologue\n");
    print("    PUSH_FP\n");     /* Save caller's frame pointer */
    print("    TSF\n");         /* FP = SP (new frame base) */

    /* Initialize register allocation */
    usedmask[IREG] = 0;
    freemask[IREG] = tmask[IREG];

    /* Set up parameter offsets
     * Stack layout after prologue:
     *   [FP+4+n] = argument n
     *   [FP+4]   = first argument
     *   [FP+2]   = return address (high byte)
     *   [FP+1]   = return address (low byte)  -- CALL pushed this
     *   [FP+0]   = saved FP (high byte)
     *   [FP-1]   = saved FP (low byte)        -- PUSH_FP pushed this
     *   [FP-2]   = first local
     *   ...
     */
    param_offset = 4;  /* Skip saved FP (2 bytes) + return address (2 bytes) */
    for (i = 0; callee[i]; i++) {
        Symbol p = callee[i];
        Symbol q = caller[i];
        p->x.offset = q->x.offset = param_offset;
        p->x.name = q->x.name = stringf("%d", param_offset);
        p->sclass = q->sclass = AUTO;
        param_offset += roundup(q->type->size, 1);
    }

    /* Generate code for function body */
    offset = maxoffset = 0;
    gencode(caller, callee);

    /* Allocate space for local variables by pushing zeros */
    if (maxoffset > 0) {
        print("    ; Allocate %d bytes for locals\n", maxoffset);
        for (i = 0; i < maxoffset; i++) {
            print("    LDI 0\n");
            print("    PUSH\n");
        }
    }

    /* Emit the generated code */
    emitcode();

    /* Epilogue - Standard C function exit
     * TFS:     SP = FP (deallocate locals)
     * POP_FP:  Restore caller's frame pointer
     * RET:     Pop return address and jump to it
     */
    print("    ; Epilogue\n");
    print("    TFS\n");         /* SP = FP (deallocate locals) */
    print("    POP_FP\n");      /* Restore caller's FP */
    print("    RET\n");
}
```

**Example: Generated code for a simple function**

```c
char add(char a, char b) {
    char result = a + b;
    return result;
}
```

Generates:

```assembly
; Function: add
_add:
    ; Prologue
    PUSH_FP             ; Save caller's frame pointer
    TSF                 ; FP = SP
    ; Allocate 1 byte for 'result'
    LDI 0
    PUSH
    ; Load a (at FP+4)
    LDA 4,FP
    ; Add b (at FP+5)
    ADD 5,FP
    ; Store to result (at FP-1)
    STA -1,FP
    ; Return result
    LDA -1,FP
    ; Epilogue
    TFS                 ; SP = FP
    POP_FP              ; Restore caller's FP
    RET
```

### Register Mapping

```c
static Symbol rmap(int opk) {
    return intregw;  /* All operations use the accumulator */
}
```

### Target and Clobber (Register Allocation Hints)

```c
static void target(Node p) {
    switch (specific(p->op)) {
    case CALL+I:
    case CALL+U:
    case CALL+P:
    case CALL+V:
        setreg(p, intreg[REG_AC]);
        break;
    case RET+I:
    case RET+U:
    case RET+P:
        rtarget(p, 0, intreg[REG_AC]);
        break;
    }
}

static void clobber(Node p) {
    switch (specific(p->op)) {
    case CALL+I:
    case CALL+U:
    case CALL+P:
    case CALL+V:
        spill(0xFF, IREG, p);  /* Calls clobber all registers */
        break;
    }
}
```

### Block Memory Operations (Stubs)

```c
static void blkfetch(int k, int off, int reg, int tmp) { }
static void blkstore(int k, int off, int reg, int tmp) { }
static void blkloop(int dreg, int doff, int sreg, int soff,
                    int size, int tmps[]) { }
```

### Emit Callback

```c
static void emit2(Node p) { }
static void doarg(Node p) { }
```

---

## Step 6: Register Management

### The Interface Structure

The Interface structure defines your backend's configuration:

```c
Interface neanderxIR = {
    /* Type metrics: {size, align, outofline} */
    1, 1, 0,    /* char:        1 byte, 1-byte align */
    2, 2, 0,    /* short:       2 bytes, 2-byte align (16-bit native) */
    2, 2, 0,    /* int:         2 bytes, 2-byte align (16-bit native) */
    4, 2, 0,    /* long:        4 bytes, 2-byte align (32-bit) */
    4, 2, 0,    /* long long:   4 bytes, 2-byte align (32-bit) */
    0, 1, 1,    /* float:       not supported */
    0, 1, 1,    /* double:      not supported */
    0, 1, 1,    /* long double: not supported */
    2, 2, 0,    /* pointer:     2 bytes, 2-byte align (16-bit address) */
    0, 2, 0,    /* struct:      2-byte alignment */

    /* Flags */
    1,          /* little_endian */
    0,          /* mulops_calls */
    0,          /* wants_callb */
    1,          /* wants_argb */
    0,          /* left_to_right */
    0,          /* wants_dag */
    1,          /* unsigned_char */

    /* Interface functions */
    address,
    blockbeg,
    blockend,
    defaddress,
    defconst,
    defstring,
    defsymbol,
    emit,
    export,
    function,
    gen,
    global,
    import,
    local,
    progbeg,
    progend,
    segment,
    space,

    /* Stabsym functions (for debugging info) */
    0, 0, 0, 0, 0, 0, 0,

    /* Code generator extensions */
    {
        1,              /* max_unaligned_load */
        rmap,
        blkfetch, blkstore, blkloop,
        _label,
        _rule,
        _nts,
        _kids,
        _string,
        _templates,
        _isinstruction,
        _ntname,
        emit2,
        doarg,
        target,
        clobber,
    }
};
```

### Understanding Register Wildcards

LCC uses "wildcards" for register allocation. A wildcard represents a set of interchangeable registers:

```c
/* Create an array of register symbols */
static Symbol intreg[32];

/* In progbeg(): */
intreg[REG_AC] = mkreg("AC", REG_AC, 1, IREG);

/* Create wildcard from array */
intregw = mkwildcard(intreg);
```

For NEANDER-X with only one accumulator, the wildcard still needs to be properly initialized using an array.

---

## Step 7: Calling Conventions

NEANDER-X's dedicated frame pointer instructions (`PUSH_FP`, `POP_FP`, `TSF`, `TFS`) enable standard C calling conventions.

### Stack Frame Layout

```
High addresses
+------------------+
| Argument N       | [FP + 4 + N-1]   <- Last argument pushed first
| ...              |
| Argument 2       | [FP + 5]
| Argument 1       | [FP + 4]         <- First argument (closest to FP)
+------------------+
| Return Addr Hi   | [FP + 3]         <- CALL pushes 16-bit return address
| Return Addr Lo   | [FP + 2]
+------------------+
| Saved FP Hi      | [FP + 1]         <- PUSH_FP saves 16-bit FP
| Saved FP Lo      | [FP + 0]         <- FP points here after TSF
+------------------+
| Local 1          | [FP - 1]         <- First local variable
| Local 2          | [FP - 2]
| ...              |
+------------------+ <- SP (current stack pointer)
Low addresses
```

### Calling Sequence

**Caller (before CALL):**
```assembly
    ; Call func(a, b) where a and b are 1-byte values
    LDA b           ; Load second argument
    PUSH            ; Push b
    LDA a           ; Load first argument
    PUSH            ; Push a
    CALL _func      ; Pushes 16-bit return address, jumps to func
    ; After return, clean up stack
    POP             ; Discard a
    POP             ; Discard b
    ; Result is in AC
```

**Callee (function entry/exit):**
```assembly
_func:
    ; Prologue
    PUSH_FP         ; Save caller's frame pointer (2 bytes)
    TSF             ; FP = SP (establish new frame)

    ; Allocate locals (if any)
    LDI 0
    PUSH            ; Allocate 1 byte for local

    ; Access parameters using FP-indexed addressing
    LDA 4,FP        ; Load first parameter (a)
    ADD 5,FP        ; Add second parameter (b)
    STA -1,FP       ; Store to local variable

    ; ... function body ...

    ; Epilogue
    LDA -1,FP       ; Load return value to AC
    TFS             ; SP = FP (deallocate locals)
    POP_FP          ; Restore caller's FP
    RET             ; Pop return address and jump
```

### Return Values

| Size | Location | Notes |
|------|----------|-------|
| 8-bit | AC | Standard return register |
| 16-bit | Y:AC | Y = high byte, AC = low byte (matches MUL output) |

### Register Preservation

| Register | Caller-saved | Callee-saved |
|----------|--------------|--------------|
| AC | Yes | - |
| X | Yes | - |
| Y | Yes | - |
| FP | - | Yes (via PUSH_FP/POP_FP) |
| SP | - | Automatically restored |

---

## Step 8: Compiling and Using the NEANDER-X Backend

This section provides detailed instructions on how to build and use the LCC compiler with the NEANDER-X backend.

### Building from Source

**1. Clone and prepare the source:**

```bash
git clone https://github.com/drh/lcc.git
cd lcc
```

**2. Ensure your backend files are in place:**
- `src/neanderx.md` - Machine description file
- `src/bind.c` - Modified to include neanderx target
- `etc/neanderx.c` - Driver configuration (optional)

**3. Build the compiler:**

```bash
# Build using make
make clean
make rcc BUILDDIR=build TARGET=neanderx

# This generates:
# - build/lburg     (grammar processor tool)
# - build/neanderx.c (generated from neanderx.md)
# - build/rcc       (the compiler)
```

**4. Verify the build:**

```bash
./build/rcc -target=neanderx --help
```

### Compiling C Programs

**Basic usage:**

```bash
# Compile a C file to NEANDER-X assembly
./build/rcc -target=neanderx myprogram.c > myprogram.asm

# Or output to specific file
./build/rcc -target=neanderx myprogram.c -o myprogram.asm
```

**With preprocessing (if cpp is available):**

```bash
# Preprocess first, then compile
cpp myprogram.c | ./build/rcc -target=neanderx > myprogram.asm
```

**Useful compiler flags:**

| Flag | Description |
|------|-------------|
| `-target=neanderx` | Select the NEANDER-X backend |
| `-d` | Enable debug output (if implemented in backend) |
| `-v` | Verbose mode |
| `-S` | Generate assembly (default for rcc) |

### Example Workflow

```bash
# 1. Write your C program
cat > test.c << 'EOF'
char add(char a, char b) {
    return a + b;
}

char main(void) {
    return add(3, 5);
}
EOF

# 2. Compile to NEANDER-X assembly
./build/rcc -target=neanderx test.c > test.asm

# 3. View the generated assembly
cat test.asm

# 4. Assemble and run on NEANDER-X simulator/hardware
# (depends on your assembler/simulator setup)
```

### Verifying Generated Code

Use the symbolic backend to see what IR operations your program generates:

```bash
./build/rcc -target=symbolic test.c
```

This shows the intermediate representation before instruction selection, helping you verify your backend handles all required operations.

---

## Step 9: Testing Your Backend

### Test with Simple Programs

**test1.c - Return constant:**
```c
char main(void) {
    return 42;
}
```

```bash
./build/rcc -target=neanderx test1.c
```

**test2.c - Parameters:**
```c
char identity(char x) {
    return x;
}
```

**test3.c - Local variables:**
```c
char main(void) {
    char x = 5;
    return x;
}
```

**test4.c - Arithmetic:**
```c
char add1(char x) {
    return x + 1;
}
```

### Using the Symbolic Backend for Debugging

The `symbolic` backend shows the IR tree before instruction selection:

```bash
./build/rcc -target=symbolic test.c
```

This helps you understand what terminals your backend needs to handle.

### Common Test Cases

1. Constants and immediates
2. Global variables
3. Local variables
4. Function parameters
5. Arithmetic operations
6. Comparisons and branches
7. Loops (while, for)
8. Function calls
9. Arrays
10. Pointers

---

## Tips and Tricks

This section covers advanced debugging techniques and common issues encountered when porting LCC to a new architecture, using the NEANDER-X backend development as a case study.

### Understanding the IR Tree Structure

The most important skill when debugging LCC backends is understanding the actual IR tree structure. What you expect the tree to look like and what it actually looks like can be very different.

**Use dflag for detailed debugging:**

In `src/gen.c`, there's a debug flag that shows the actual IR trees being matched:

```c
// In src/gen.c, temporarily change:
int dflag = 1;  // Enable debug output (normally 0)
```

When enabled, you'll see output like:

```
dumpcover: n=0x... ADDI1
  l=0x... LOADI1
    l=0x... INDIRU1
      l=0x... ADDRLP2
  r=0x... LOADI1
    l=0x... INDIRU1
      l=0x... ADDRLP2
```

This reveals the **actual** tree structure the compiler is trying to match.

### The LOAD Node Wrapper Problem

**Problem:** You write rules like:
```
reg: ADDI1(INDIRU1(addr),INDIRU1(addr))  "    LDA %0\n    ADD %1\n"  2
```

But the compiler generates `LDA -1; LDA -2; ADDX` instead of `LDA -1; ADD -2`.

**Root Cause:** LCC inserts LOAD nodes between arithmetic operations and memory accesses. The actual tree is:
```
ADDI1(LOADI1(INDIRU1(addr)), LOADI1(INDIRU1(addr)))
```

**Solution:** Add rules that match the LOAD wrappers:
```
reg: ADDI1(LOADI1(INDIRU1(addr)),LOADI1(INDIRU1(addr)))  "    LDA %0\n    ADD %1\n"  2
reg: SUBI1(LOADI1(INDIRU1(addr)),LOADI1(INDIRU1(addr)))  "    LDA %0\n    SUB %1\n"  2
```

The `LOADI1`/`LOADU1` terminals wrap memory loads and are required for proper matching.

### The unsigned_char Flag Impact

**Problem:** Your rules match `INDIRI1` but the compiler uses `INDIRU1`.

**Root Cause:** The `unsigned_char` flag in the Interface structure determines whether `char` is signed or unsigned:

```c
Interface neanderxIR = {
    // ...
    1,          /* unsigned_char - if 1, char is unsigned */
    // ...
};
```

When `unsigned_char = 1`:
- `char` variables use `INDIRU1` (unsigned load)
- Rules must match `INDIRU1`, not `INDIRI1`

**Solution:** Add rules for both signed and unsigned variants, or ensure your `unsigned_char` setting matches your rules.

### Pointer Arithmetic (ADDP2) for Array Indexing

**Problem:** Array access like `arr[i]` causes "Bad terminal 2359" error.

**Root Cause:** Array indexing involves pointer arithmetic. `arr[i]` becomes `*(arr + i)`, which generates an `ADDP2` (pointer add) node. Terminal 2359 = ADDP2.

**Solution:** Add the ADDP2 terminal and rules:

```
%term ADDP2=2359

/* Pointer arithmetic for array indexing */
addr: ADDP2(addr,reg)  "%0"  1

/* Load through indexed pointer */
reg: INDIRI1(ADDP2(addr,reg))  "    TAX\n    LDA %0,X\n"  3
reg: INDIRU1(ADDP2(addr,reg))  "    TAX\n    LDA %0,X\n"  3

/* Store through indexed pointer */
stmt: ASGNI1(ADDP2(addr,reg),reg)  "    TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n"  5
stmt: ASGNU1(ADDP2(addr,reg),reg)  "    TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n"  5
```

### Operand Ordering in Tree Patterns

**Problem:** Your rules work for `base + index` but fail for `index + base`.

**Root Cause:** The compiler may generate `ADDP2(index, base)` instead of `ADDP2(base, index)`. For example, `arr[i]` might generate:
```
ADDP2(CVUU2(INDIRU1(ADDRLP2(i))), ADDRGP2(arr))
```

This is `index + base`, not `base + index`!

**Solution:** Add rules for both operand orderings:

```
/* base + index */
reg: INDIRU1(ADDP2(addr,reg))  "    TAX\n    LDA %0,X\n"  3

/* index + base (reversed operands - use %1 for base address) */
reg: INDIRU1(ADDP2(reg,addr))  "    TAX\n    LDA %1,X\n"  3

/* Store with reversed operands */
stmt: ASGNI1(ADDP2(reg,addr),reg)  "    TAY\n    POP\n    TAX\n    TYA\n    STA %1,X\n"  5
stmt: ASGNU1(ADDP2(reg,addr),reg)  "    TAY\n    POP\n    TAX\n    TYA\n    STA %1,X\n"  5
```

Note how `%1` is used instead of `%0` to reference the second child (the address).

### Using _decode_reg for Rule Debugging

When you see confusing rule numbers in debug output, use the `_decode_reg` array in the generated `.c` file to map internal rule numbers to template rules:

```bash
# Look at the generated backend code
grep -A 10 "_decode" build/neanderx.c
```

This helps understand which grammar rules are being selected.

### Debugging "Bad terminal" Errors

**When you see "Bad terminal XXXX":**

1. Calculate what operation it represents:
   - terminal = size * 1024 + op * 16 + type + 5
   - size: 1, 2, 4, or 8
   - op: operation number from ops.h
   - type: I=0, U=1, P=2

2. Look up the operation in `src/ops.h`

3. Add the terminal definition and rule

**Common missing terminals:**
| Terminal | Number | Description |
|----------|--------|-------------|
| ADDP2 | 2359 | Pointer addition (array indexing) |
| SUBP2 | 2375 | Pointer subtraction |
| CVUU2 | 2230 | Convert unsigned to unsigned 2-byte |
| CVPU2 | 2231 | Convert pointer to unsigned 2-byte |

### Expression Temporaries and Register Pressure

**Problem:** Complex expressions fail with "can't find a reg" or generate inefficient code.

**Solution:** For accumulator-based architectures, use X and Y registers as expression temporaries:

```
reg: ADDI1(reg,reg)  "    TAX\n    POP\n    ADDX\n"  3
```

This pattern:
1. Saves right operand to X (`TAX`)
2. Pops left operand from stack to AC (`POP`)
3. Performs the operation (`ADDX`)

### Testing Incrementally

**Recommended testing order:**

1. **Constants and returns:**
   ```c
   char main(void) { return 42; }
   ```

2. **Local variables:**
   ```c
   char main(void) { char x = 5; return x; }
   ```

3. **Simple arithmetic:**
   ```c
   char main(void) { char a = 3, b = 2; return a + b; }
   ```

4. **Function calls:**
   ```c
   char add(char a, char b) { return a + b; }
   char main(void) { return add(3, 5); }
   ```

5. **Arrays with constant indices:**
   ```c
   char arr[3];
   char main(void) { arr[0] = 1; return arr[0]; }
   ```

6. **Arrays with variable indices:**
   ```c
   char arr[3];
   char main(void) { char i = 1; arr[i] = 5; return arr[i]; }
   ```

7. **Loops:**
   ```c
   char main(void) { char i = 0; while (i < 10) i = i + 1; return i; }
   ```

8. **Pointers:**
   ```c
   char x;
   char main(void) { char *p = &x; *p = 42; return x; }
   ```

---

## Common Pitfalls and Solutions

### Critical: VREG Memory Slot Management

**Problem:** Virtual registers (VREGs) are used by LCC for expression temporaries. In accumulator architectures, these must be spilled to memory. A common mistake is hardcoding VREG offsets separately from local variable allocation.

**Symptoms:**
- Tests pass individually but fail when combined
- Recursive functions produce wrong results
- Values mysteriously get overwritten
- Works for simple functions but fails for complex ones

**Root Cause:** The `emit2()` function might use a separate offset calculation (like `VREG_OFFSET(slot)`) while `local()` allocates variables at different offsets. This causes VREGs and local variables to overlap in memory.

**Example of the bug:**
```c
/* BAD: Using hardcoded VREG offsets */
#define VREG_OFFSET(slot) (vreg_base_offset + (slot) * 2)

static void emit2(Node p) {
    if (LEFT_CHILD(p)->op == VREG+P) {
        int slot = get_vreg_slot(reg);
        print("    STA %d,FP\n", VREG_OFFSET(slot));  /* WRONG! */
    }
}
```

**Solution:** Use the symbol's `x.name` field which is set by `local()` with the correct offset:

```c
/* CORRECT: Use the symbol's allocated offset */
static void emit2(Node p) {
    if (LEFT_CHILD(p)->op == VREG+P) {
        Symbol reg = LEFT_CHILD(p)->syms[0];
        if (reg && reg->x.name) {
            print("    STA %s,FP\n", reg->x.name);  /* Uses local()'s offset */
        }
    }
}
```

This ensures VREGs are allocated through the same mechanism as local variables, preventing overlap.

### Critical: Stack Allocation in 16-bit Mode

**Problem:** When allocating stack space for local variables, the allocation loop must account for the word size.

**Symptoms:**
- Recursive functions timeout or produce wrong results
- Stack corruption
- Functions work but nested calls fail
- Fibonacci, factorial, and similar recursive tests fail

**Root Cause:** The stack allocation loop runs once per byte of `maxoffset`, but PUSH is a 16-bit (2-byte) operation:

**Example of the bug:**
```c
/* BAD: Allocates double the needed space */
if (maxoffset > 0) {
    for (i = 0; i < maxoffset; i++) {  /* WRONG! */
        print("    LDI 0\n");
        print("    PUSH\n");  /* Each PUSH is 2 bytes */
    }
}
```

If `maxoffset = 4`, this pushes 4 times × 2 bytes = 8 bytes, causing stack corruption.

**Solution:** Step by the word size (2 bytes for 16-bit):

```c
/* CORRECT: Account for 16-bit PUSH */
if (maxoffset > 0) {
    for (i = 0; i < maxoffset; i += 2) {  /* Step by 2 */
        print("    LDI 0\n");
        print("    PUSH\n");
    }
}
```

### 1. "Bad terminal XXXX"

**Problem:** The compiler encounters an IR operation your backend doesn't handle.

**Solution:** Add the terminal definition and a grammar rule for it. Use the symbolic backend to see what operations are generated.

### 2. "Bad goal nonterminal 0"

**Problem:** A grammar rule has an empty template `""` for what should be an instruction.

**Solution:** Use a comment template instead: `"# description\n"`

### 3. Segmentation Fault in Register Allocation

**Problem:** `mkwildcard` was called with a single symbol pointer instead of an array.

**Solution:** Use an array:
```c
static Symbol intreg[32];
intreg[0] = mkreg("AC", 0, 1, IREG);
intregw = mkwildcard(intreg);  /* Pass the array */
```

### 4. C Type Promotion Issues

**Problem:** Even for `char` operations, the compiler generates 4-byte (ADDI4, RETI4) operations.

**Solution:** Add rules for 4-byte terminals that perform 8-bit operations:
```c
reg: ADDI4(reg,reg)  "    ADD ...\n"  5
stmt: RETI4(reg)     "# ret\n"  0
```

### 5. Infinite Loop During Compilation

**Problem:** The compiler hangs on certain expressions.

**Solution:** Check for missing rules that would cause the labeling phase to fail. Ensure all necessary conversions (CVII4, CVII1) are handled.

### 6. Wrong Terminal Numbers

**Problem:** Instructions are not being matched correctly.

**Solution:** Verify terminal numbers match LCC's encoding:
```
terminal = size * 1024 + (op - 1) * 16 + type + 5
```

Compare with existing backends like x86linux.md.

### 7. Wrong Code Generated for Binary Operations

**Problem:** `a + b` generates two loads followed by a register-to-register add instead of using memory operand.

**Solution:** The IR tree has LOAD wrappers. Add rules that match `LOADI1(INDIRU1(addr))` patterns. See "The LOAD Node Wrapper Problem" above.

### 8. Array Indexing Fails

**Problem:** `arr[i]` with variable index fails with "Bad terminal 2359".

**Solution:** Add `ADDP2` terminal and pointer arithmetic rules. See "Pointer Arithmetic (ADDP2)" above.

### 9. Rules Match Sometimes But Not Others

**Problem:** Same pattern works in some contexts but fails in others.

**Solution:** Operand ordering may vary. Add rules for both `ADDP2(addr,reg)` and `ADDP2(reg,addr)`. See "Operand Ordering in Tree Patterns" above.

---

## References

### Official Documentation

- **LCC GitHub Repository**: https://github.com/drh/lcc
- **LCC Official Website**: https://drh.github.io/lcc/
- **LCC Interface v4 Documentation**: https://drh.github.io/lcc/documents/interface4.pdf
- **Installation Guide**: https://htmlpreview.github.io/?https://raw.githubusercontent.com/drh/lcc/master/doc/install.html

### Books

- **A Retargetable C Compiler: Design and Implementation** by Chris Fraser and David Hanson (Addison-Wesley, 1995, ISBN 0-8053-1670-1) - The definitive guide to LCC internals

### Tutorials and Examples

- **Retargeting LCC for Magic-1**: https://www.homebrewcpu.com/retargeting_lcc.htm - Excellent practical guide for porting to an 8/16-bit homebrew CPU
- **LCC NEANDER-X Backend**: This repository's `src/neanderx.md` - A complete working example

### Community

- **comp.compilers.lcc**: https://groups.google.com/group/comp.compilers.lcc - USENET newsgroup for LCC discussion

### NEANDER-X Specific

- **NEANDER-X CPU Documentation**: See the main project's README.md and docs/ folder
- **Instruction Set Reference**: docs/NEANDER_ISA.md in the main project

---

## Appendix A: Complete Terminal Number Reference

| Terminal | Number | Calculation |
|----------|--------|-------------|
| CNSTI1 | 1045 | 1*1024 + 0*16 + 0 + 21 |
| CNSTU1 | 1046 | 1*1024 + 0*16 + 1 + 21 |
| CNSTI4 | 4117 | 4*1024 + 0*16 + 0 + 21 |
| ARGI1 | 1061 | 1*1024 + 1*16 + 0 + 21 |
| ASGNI1 | 1077 | 1*1024 + 2*16 + 0 + 21 |
| INDIRI1 | 1093 | 1*1024 + 3*16 + 0 + 21 |
| ADDI1 | 1333 | 1*1024 + 18*16 + 0 + 21 |
| SUBI1 | 1349 | 1*1024 + 19*16 + 0 + 21 |
| MULI1 | 1493 | 1*1024 + 28*16 + 0 + 21 |
| DIVI1 | 1477 | 1*1024 + 27*16 + 0 + 21 |
| LOADI1 | 1253 | 1*1024 + 13*16 + 0 + 21 |
| RETI1 | 1269 | 1*1024 + 14*16 + 0 + 21 |
| ADDRGP2 | 2311 | 2*1024 + 15*16 + 2 + 21 |
| ADDRFP2 | 2327 | 2*1024 + 16*16 + 2 + 21 |
| ADDRLP2 | 2343 | 2*1024 + 17*16 + 2 + 21 |
| JUMPV | 584 | Special encoding |
| LABELV | 600 | Special encoding |

---

## Appendix B: Debugging Tips

### Enable Debug Output

Add `-d` flag handling in progbeg():
```c
static int dflag = 0;

static void progbeg(int argc, char *argv[]) {
    int i;
    for (i = 1; i < argc; i++)
        if (strcmp(argv[i], "-d") == 0)
            dflag = 1;
    /* ... */
}
```

### Print IR Trees

Use the symbolic backend to see what the front-end generates:
```bash
./build/rcc -target=symbolic yourfile.c
```

### Check Grammar Coverage

If compilation fails on a specific construct, look at the symbolic output to identify which terminals are needed.

### Use GDB/LLDB

For crashes:
```bash
lldb -- ./build/rcc -target=neanderx test.c
(lldb) run
(lldb) bt
```

---

*This document was created as part of the NEANDER-X educational processor project.*
