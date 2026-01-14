# Porting LCC to the NEANDER-X Processor: A Complete Tutorial

This document provides a comprehensive, step-by-step guide to porting the LCC (Little C Compiler) to the NEANDER-X 8-bit educational processor. Whether you're a student learning about compilers or a hobbyist building your own CPU, this tutorial will walk you through the entire process.

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
12. [Step 8: Testing Your Backend](#step-8-testing-your-backend)
13. [Common Pitfalls and Solutions](#common-pitfalls-and-solutions)
14. [References](#references)

---

## Introduction

LCC is a retargetable ANSI C compiler originally developed by Chris Fraser and David Hanson. "Retargetable" means you can adapt it to generate code for different processor architectures by writing a new backend. This tutorial documents the process of creating a backend for the NEANDER-X, an 8-bit educational processor.

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

The NEANDER-X is an 8-bit educational processor with these characteristics:

### Registers

| Register | Size | Description |
|----------|------|-------------|
| AC | 8-bit | Accumulator - main computation register |
| X | 8-bit | Index register |
| Y | 8-bit | Index register / MUL high byte |
| PC | 16-bit | Program counter |
| SP | 16-bit | Stack pointer |
| FP | 16-bit | Frame pointer |

### Condition Flags

- **N** (Negative): Set when result is negative
- **Z** (Zero): Set when result is zero
- **C** (Carry): Set on carry/borrow

### Key Instructions

```
LDA addr    ; Load AC from memory
STA addr    ; Store AC to memory
LDI imm     ; Load immediate to AC
ADD addr    ; AC = AC + mem[addr]
SUB addr    ; AC = AC - mem[addr]
AND/OR/XOR  ; Bitwise operations
MUL         ; AC * X -> AC (low), Y (high)
DIV/MOD     ; Division and modulo
PUSH/POP    ; Stack operations
CALL/RET    ; Subroutine calls
JMP/JZ/JN   ; Jumps and branches
```

### Memory Model

- 16-bit address space (64KB via SPI SRAM)
- 8-bit data bus
- Stack grows downward

### Challenges for C Compilation

1. **Single Accumulator**: Only one main register for computation
2. **8-bit Native Size**: C promotes to int (typically 32-bit)
3. **Limited Addressing Modes**: No complex addressing
4. **No Hardware Multiply for Large Types**: Multi-byte operations need software

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

/* Load from frame pointer offset */
reg: INDIRI1(ADDRFP2)  "    LDA_FP %a\n"  2
reg: INDIRI1(ADDRLP2)  "    LDA_FP %a\n"  2

/* Store to memory */
stmt: ASGNI1(addr,reg)  "    STA %0\n"  2
stmt: ASGNU1(addr,reg)  "    STA %0\n"  2

/* Store to frame pointer offset */
stmt: ASGNI1(ADDRFP2,reg)  "    STA_FP %a\n"  2
stmt: ASGNI1(ADDRLP2,reg)  "    STA_FP %a\n"  2
```

### Arithmetic Rules

```
/* Addition: reg + reg */
reg: ADDI1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    ADD _tmp\n"  5
reg: ADDU1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    ADD _tmp\n"  5
reg: ADDI4(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    ADD _tmp\n"  5

/* Addition with memory operand (more efficient) */
reg: ADDI1(reg,INDIRI1(addr))  "    ADD %1\n"  2

/* Increment (special case for +1) */
conN: CNSTI1  "%a"  range(a, 1, 1)
reg: ADDI1(reg,conN)  "    INC\n"  1

/* Subtraction */
reg: SUBI1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    SUB _tmp\n"  5
reg: SUBI1(reg,INDIRI1(addr))  "    SUB %1\n"  2
reg: SUBI1(reg,conN)  "    DEC\n"  1

/* Multiplication */
reg: MULI1(reg,reg)  "    PUSH\n    TAX\n    POP\n    MUL\n"  5

/* Division and Modulo */
reg: DIVI1(reg,reg)  "    PUSH\n    TAX\n    POP\n    DIV\n"  5
reg: MODI1(reg,reg)  "    PUSH\n    TAX\n    POP\n    MOD\n"  5

/* Negation */
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

```
/* Labels */
stmt: LABELV  "%a:\n"

/* Unconditional jump */
stmt: JUMPV(addr)  "    JMP %0\n"  1

/* Comparisons and conditional branches */
stmt: EQI1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    CMP _tmp\n    JZ %a\n"  6
stmt: NEI1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    CMP _tmp\n    JNZ %a\n" 6
stmt: LTI1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    CMP _tmp\n    JN %a\n"  6

/* Optimized comparison with memory */
stmt: EQI1(reg,INDIRI1(addr))  "    CMP %1\n    JZ %a\n"  3
stmt: NEI1(reg,INDIRI1(addr))  "    CMP %1\n    JNZ %a\n" 3
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

```c
static void function(Symbol f, Symbol caller[], Symbol callee[], int ncalls) {
    int i;
    int param_offset;

    print("\n; Function: %s\n", f->name);
    print("%s:\n", f->x.name);

    /* Prologue */
    print("    ; Prologue\n");
    print("    PUSH_FP\n");     /* Save caller's frame pointer */
    print("    TSF\n");         /* FP = SP */

    /* Initialize register allocation */
    usedmask[IREG] = 0;
    freemask[IREG] = tmask[IREG];

    /* Set up parameter offsets */
    param_offset = 4;  /* Skip saved FP (2) + return address (2) */
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

    /* Allocate space for local variables */
    if (maxoffset > 0) {
        print("    ; Allocate %d bytes for locals\n", maxoffset);
        for (i = 0; i < maxoffset; i++) {
            print("    LDI 0\n");
            print("    PUSH\n");
        }
    }

    /* Emit the generated code */
    emitcode();

    /* Epilogue */
    print("    ; Epilogue\n");
    print("    TFS\n");         /* SP = FP */
    print("    POP_FP\n");      /* Restore caller's FP */
    print("    RET\n");
}
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
    1, 1, 0,    /* char */
    1, 1, 0,    /* short */
    1, 1, 0,    /* int - 8-bit for NEANDER-X */
    2, 1, 0,    /* long - 16-bit */
    2, 1, 0,    /* long long */
    0, 1, 1,    /* float - not supported */
    0, 1, 1,    /* double - not supported */
    0, 1, 1,    /* long double - not supported */
    2, 1, 0,    /* pointer - 16-bit */
    0, 1, 0,    /* struct */

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

### Stack Frame Layout

```
High addresses
+------------------+
| Argument N       | [FP + N+3]
| ...              |
| Argument 1       | [FP + 4]
+------------------+
| Return Addr Hi   | [FP + 3]
| Return Addr Lo   | [FP + 2]
+------------------+
| Saved FP Hi      | [FP + 1]
| Saved FP Lo      | [FP + 0] <- FP points here
+------------------+
| Local 1          | [FP - 1]
| Local 2          | [FP - 2]
| ...              |
+------------------+ <- SP
Low addresses
```

### Calling Sequence

**Caller:**
1. Push arguments right-to-left
2. Execute CALL instruction (pushes return address)
3. On return, pop arguments to clean up stack

**Callee:**
1. Save FP (PUSH_FP)
2. Set FP = SP (TSF)
3. Allocate local variables
4. Execute function body
5. Set SP = FP (TFS)
6. Restore FP (POP_FP)
7. Return (RET)

### Return Values

- 8-bit values: In AC register
- 16-bit values: Low byte in AC, high byte in Y

---

## Step 8: Testing Your Backend

### Build the Compiler

```bash
cd lcc
make clean
make rcc BUILDDIR=build TARGET=neanderx
```

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

## Common Pitfalls and Solutions

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
