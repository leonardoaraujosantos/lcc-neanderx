# LCC Complete Tutorial: Porting a C Compiler to Your CPU

A comprehensive guide to understanding, building, and porting the LCC (Little C Compiler) to custom CPU architectures.

## Table of Contents

1. [Introduction to LCC](#introduction-to-lcc)
2. [LCC Architecture and Internals](#lcc-architecture-and-internals)
3. [CPU Requirements for C Compiler Support](#cpu-requirements-for-c-compiler-support)
4. [Setting Up the Development Environment](#setting-up-the-development-environment)
5. [Understanding the LCC Source Code](#understanding-the-lcc-source-code)
6. [The Machine Description Language (lburg)](#the-machine-description-language-lburg)
7. [Creating Your Backend: Step-by-Step](#creating-your-backend-step-by-step)
8. [Terminal Definitions: Complete Reference](#terminal-definitions-complete-reference)
9. [Writing Grammar Rules](#writing-grammar-rules)
10. [Implementing Interface Functions](#implementing-interface-functions)
11. [Register Allocation and Management](#register-allocation-and-management)
12. [Calling Conventions Design](#calling-conventions-design)
13. [Building and Compiling](#building-and-compiling)
14. [Debugging Your Backend](#debugging-your-backend)
15. [Testing Strategies](#testing-strategies)
16. [Advanced Topics](#advanced-topics)
17. [Troubleshooting Guide](#troubleshooting-guide)
18. [Complete Example: 8-bit CPU Backend](#complete-example-8-bit-cpu-backend)
19. [References and Resources](#references-and-resources)

---

## Introduction to LCC

### What is LCC?

LCC (Little C Compiler) is a retargetable ANSI C compiler developed by Chris Fraser and David Hanson. "Retargetable" means the compiler can generate code for different processor architectures by writing a new backend, without modifying the compiler's front-end.

### Why Choose LCC?

| Feature | Benefit |
|---------|---------|
| **Small codebase** | ~12,000 lines of C, easy to understand |
| **Well documented** | Book and papers available |
| **Simple backend interface** | ~400-600 lines for a new target |
| **ANSI C compliant** | Supports standard C89 |
| **Proven design** | Used in production and education |
| **No external dependencies** | Self-contained build |

### LCC vs Other Compilers

| Compiler | Lines of Code | Backend Complexity | Best For |
|----------|---------------|-------------------|----------|
| LCC | ~12K | Low (~500 lines) | 8/16-bit CPUs, education |
| SDCC | ~100K | Medium | 8-bit micros (8051, Z80) |
| GCC | ~15M | Very High | Production systems |
| LLVM | ~10M | High | Modern architectures |

For hobby CPUs and educational purposes, LCC offers the best complexity-to-capability ratio.

### What You'll Learn

By the end of this tutorial, you will be able to:

1. Understand LCC's internal architecture
2. Evaluate if your CPU can support C compilation
3. Write a complete LCC backend for your processor
4. Debug and test the backend thoroughly
5. Generate working assembly code from C programs

---

## LCC Architecture and Internals

### Compilation Pipeline

```
┌─────────────┐     ┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│   C Source  │────▶│ Preprocessor│────▶│  Front-end  │────▶│   Backend   │
│    (.c)     │     │    (cpp)    │     │   (parser)  │     │   (yours)   │
└─────────────┘     └─────────────┘     └─────────────┘     └─────────────┘
                                              │                    │
                                              ▼                    ▼
                                        ┌─────────────┐     ┌─────────────┐
                                        │  IR Trees   │     │  Assembly   │
                                        │             │     │    (.s)     │
                                        └─────────────┘     └─────────────┘
```

### Key Components

**1. Front-end (shared by all targets):**
- Lexer and parser
- Type checking
- Intermediate representation (IR) generation

**2. Back-end (target-specific):**
- Instruction selection (pattern matching)
- Register allocation
- Code emission

**3. lburg (code generator generator):**
- Processes `.md` files (machine description)
- Generates C code for instruction selection
- Uses BURS (Bottom-Up Rewrite System) algorithm

### The Intermediate Representation

LCC uses expression trees as its IR. Each tree node represents an operation:

```
C Code:     x = a + b * c;

IR Tree:
            ASGNI
           /     \
      ADDRLP(x)  ADDI
                /    \
           INDIRI   MULI
              |    /    \
         ADDRLP(a) INDIRI INDIRI
                     |      |
                  ADDRLP(b) ADDRLP(c)
```

### Node Structure

Each IR node contains:

```c
struct node {
    short op;           // Operation code
    short count;        // Reference count
    Symbol syms[3];     // Associated symbols
    Node kids[2];       // Child nodes (left, right)
    Node link;          // Next node in forest
    Xnode x;            // Target-specific data
};
```

### Operation Encoding

Operations are encoded as: `size * 1024 + op * 16 + type + 5`

Where:
- **size**: 1, 2, 4, or 8 bytes
- **op**: Operation number (0-63)
- **type**: I=0 (signed), U=1 (unsigned), P=2 (pointer), V=3 (void), B=4 (struct), F=5 (float)

Example: `ADDI4` (4-byte signed add)
- size=4: 4 * 1024 = 4096
- op=ADD=19: 19 * 16 = 304
- type=I=0
- +5 = 5
- Total: 4096 + 304 + 0 + 5 = **4405**

---

## CPU Requirements for C Compiler Support

Before porting LCC to your CPU, evaluate these requirements:

### Minimum Requirements

| Feature | Required | Notes |
|---------|----------|-------|
| **Stack** | Essential | For function calls, locals |
| **Subroutine calls** | Essential | CALL/RET or equivalent |
| **Arithmetic** | ADD, SUB | MUL/DIV can be software |
| **Comparisons** | Flags or CMP | For conditionals |
| **Conditional jumps** | At least JZ/JNZ | More is better |
| **Memory access** | Load/Store | Direct addressing minimum |

### Recommended Features

| Feature | Benefit | Without It |
|---------|---------|------------|
| **Frame pointer** | Efficient locals/params | Complex offset tracking |
| **Index registers** | Array access | Multi-instruction sequences |
| **Multiple registers** | Expression temps | Stack-heavy code |
| **Indexed addressing** | `LDA addr,X` | Computed addresses |
| **Carry flag** | Multi-byte arithmetic | Complex sequences |
| **Hardware MUL/DIV** | Fast operations | Software routines |

### Architecture Categories

**Easy to Port (8-16 hours):**
- Multiple general-purpose registers
- Frame pointer support
- Rich addressing modes
- Examples: ARM, x86, MIPS

**Moderate Difficulty (16-40 hours):**
- Limited registers (2-4)
- Stack-based operations
- Basic addressing modes
- Examples: 6502, Z80, 8051

**Challenging (40+ hours):**
- Accumulator-only architecture
- No frame pointer
- Minimal addressing modes
- Examples: Original NEANDER, PDP-8

### Minimum Instruction Set Checklist

```
Essential Instructions:
[ ] Load immediate to register
[ ] Load from memory
[ ] Store to memory
[ ] Add
[ ] Subtract
[ ] Bitwise AND, OR, XOR (or software emulation)
[ ] Compare (sets flags)
[ ] Conditional jump (at least zero/non-zero)
[ ] Unconditional jump
[ ] Call subroutine
[ ] Return from subroutine
[ ] Push to stack
[ ] Pop from stack

Highly Recommended:
[ ] Frame pointer register
[ ] Indexed addressing (reg + offset)
[ ] Increment/Decrement
[ ] Shift left/right
[ ] Negate (two's complement)
[ ] Compare with immediate

Optional but Helpful:
[ ] Hardware multiply
[ ] Hardware divide
[ ] Signed comparison jumps
[ ] Register-to-register moves
[ ] Swap registers
```

### Data Type Support

| C Type | Typical Size | Your CPU Size | Notes |
|--------|-------------|---------------|-------|
| char | 1 byte | Must support | Basic unit |
| short | 2 bytes | Optional | Can equal int |
| int | 2 or 4 bytes | Must support | Platform word |
| long | 4 bytes | Optional | Multi-byte ops |
| pointer | 2 or 4 bytes | Must support | Address size |
| float | 4 bytes | Optional | Often software |

**For 8-bit CPUs:** It's acceptable to make `int` = `char` = 8 bits, though this deviates from standard C. Alternatively, implement 16-bit `int` using multi-byte operations.

---

## Setting Up the Development Environment

### Prerequisites

```bash
# Required tools
- C compiler (GCC or Clang)
- make
- ar (archive tool)
- Standard Unix utilities

# Optional but helpful
- gdb or lldb (debugging)
- diff (comparing outputs)
- git (version control)
```

### Getting LCC Source Code

```bash
# Clone the official repository
git clone https://github.com/drh/lcc.git
cd lcc

# Explore the structure
ls -la
```

### Directory Structure

```
lcc/
├── src/           # Compiler source code
│   ├── bind.c     # Backend binding (modify this)
│   ├── c.h        # Main header file
│   ├── gen.c      # Code generation framework
│   ├── ops.h      # Operation definitions
│   ├── config.h   # Configuration
│   └── *.md       # Machine descriptions (add yours here)
├── etc/           # Driver configurations
├── lburg/         # lburg tool source
├── doc/           # Documentation
├── cpp/           # Preprocessor
├── lib/           # Runtime libraries
└── makefile       # Build system
```

### Initial Build Test

```bash
# Build the compiler with an existing target
make BUILDDIR=build

# Verify it works
./build/rcc -target=symbolic test.c
```

---

## Understanding the LCC Source Code

### Key Source Files

| File | Purpose | Modify? |
|------|---------|---------|
| `src/c.h` | Main header, structures | Read only |
| `src/bind.c` | Target registration | Add your target |
| `src/gen.c` | Code generation | Debug flags |
| `src/ops.h` | Operation definitions | Read only |
| `lburg/lburg.c` | Grammar processor | Read only |
| `src/yourTarget.md` | Your backend | Create this |

### The Interface Structure

Every backend must define an `Interface` structure:

```c
Interface yourTargetIR = {
    /* Type sizes and alignments */
    1, 1, 0,    /* char: size, align, outofline */
    2, 2, 0,    /* short */
    4, 4, 0,    /* int */
    4, 4, 0,    /* long */
    4, 4, 0,    /* long long */
    4, 4, 1,    /* float (outofline=1 means not supported inline) */
    8, 8, 1,    /* double */
    8, 8, 1,    /* long double */
    4, 4, 0,    /* pointer */
    0, 1, 0,    /* struct (size computed per struct) */

    /* Flags */
    1,          /* little_endian (0 for big endian) */
    0,          /* mulops_calls (1 if MUL/DIV are function calls) */
    0,          /* wants_callb (1 to pass struct returns by pointer) */
    1,          /* wants_argb (1 to push struct args) */
    0,          /* left_to_right (argument evaluation order) */
    0,          /* wants_dag (1 for DAG representation) */
    0,          /* unsigned_char (1 if char is unsigned) */

    /* Function pointers */
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

    /* Debug functions (can be NULL) */
    0, 0, 0, 0, 0, 0, 0,

    /* Code generator extension */
    {
        1,              /* max_unaligned_load */
        rmap,           /* register mapping */
        blkfetch, blkstore, blkloop,
        _label,         /* generated by lburg */
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

### Important Data Structures

**Symbol structure (simplified):**
```c
struct symbol {
    char *name;         /* Symbol name */
    int scope;          /* LOCAL, GLOBAL, etc. */
    int sclass;         /* AUTO, STATIC, EXTERN, etc. */
    Type type;          /* Type information */
    struct {
        char *name;     /* Assembly name */
        int offset;     /* Stack offset for locals */
    } x;                /* Backend-specific data */
};
```

**Type structure (simplified):**
```c
struct type {
    int op;             /* Type operator (INT, POINTER, etc.) */
    int size;           /* Size in bytes */
    int align;          /* Alignment requirement */
    Type type;          /* Base type (for pointers, arrays) */
};
```

---

## The Machine Description Language (lburg)

### Overview

The `.md` (machine description) file is the heart of your backend. It's processed by `lburg` to generate C code for instruction selection.

### File Structure

```
%{
/* PROLOGUE: C declarations and helper functions */
#include "c.h"
/* ... */
%}

%start stmt    /* Starting nonterminal */

/* TERMINAL DEFINITIONS */
%term CNSTI1=1045
%term ADDI1=1333
/* ... more terminals ... */

%%

/* GRAMMAR RULES */
reg: CNSTI1  "    LDI %a\n"  1
stmt: ASGNI1(addr,reg)  "    STA %0\n"  2
/* ... more rules ... */

%%

/* EPILOGUE: Interface function implementations */
static void progbeg(int argc, char *argv[]) { /* ... */ }
/* ... */

Interface yourTargetIR = { /* ... */ };
```

### Grammar Rule Syntax

```
nonterminal: pattern  "template"  cost
```

- **nonterminal**: Target symbol (stmt, reg, addr, con, etc.)
- **pattern**: IR tree pattern to match
- **template**: Assembly code to emit
- **cost**: Relative cost (lower = preferred)

### Template Substitutions

| Marker | Meaning | Example |
|--------|---------|---------|
| `%a` | Node's symbol name | Variable name |
| `%0` | First child's result | Left operand |
| `%1` | Second child's result | Right operand |
| `%c` | Register name | "AC", "R0" |
| `%F` | Function name | For calls |
| `%%` | Literal percent | |

### Nonterminal Hierarchy

```
stmt    ← Root of expression trees (statements)
  │
  ├── reg    ← Value in a register
  │     │
  │     ├── con    ← Constant value
  │     │
  │     └── addr   ← Memory address
  │
  └── addr   ← Address expression
        │
        ├── ADDRLP  ← Local variable address
        ├── ADDRFP  ← Parameter address
        └── ADDRGP  ← Global variable address
```

### Cost Functions

Costs can be constants or expressions:

```c
/* Constant cost */
reg: ADDI1(reg,reg)  "..."  3

/* Conditional cost using helper function */
reg: ADDI1(reg,conN)  "    INC\n"  range(a, 1, 1)

/* In prologue, define: */
#define range(p, lo, hi) \
    ((p)->syms[0]->u.c.v.i >= (lo) && \
     (p)->syms[0]->u.c.v.i <= (hi) ? 0 : LBURG_MAX)
```

---

## Creating Your Backend: Step-by-Step

### Step 1: Register Your Target

Edit `src/bind.c`:

```c
/* Find the xx/yy macro list and add your target */
#define yy \
xx(alpha/osf,    alphaIR) \
xx(mips/irix,    mipsebIR) \
xx(sparc/sun,    sparcIR) \
xx(x86/linux,    x86linuxIR) \
xx(mytarget,     mytargetIR) \    /* ADD THIS */
xx(symbolic,     symbolicIR) \
xx(null,         nullIR)
```

### Step 2: Create Machine Description File

Create `src/mytarget.md`:

```c
%{
#include "c.h"

/* Required macros for lburg */
#define NODEPTR_TYPE Node
#define OP_LABEL(p) ((p)->op)
#define LEFT_CHILD(p) ((p)->kids[0])
#define RIGHT_CHILD(p) ((p)->kids[1])
#define STATE_LABEL(p) ((p)->x.state)

/* Forward declarations */
static void address(Symbol, Symbol, long);
static void defconst(int, int, Value);
static void defaddress(Symbol);
static void defstring(int, char *);
static void defsymbol(Symbol);
static void emit2(Node);
static void doarg(Node);
static void export(Symbol);
static void function(Symbol, Symbol[], Symbol[], int);
static void global(Symbol);
static void import(Symbol);
static void local(Symbol);
static void progbeg(int, char **);
static void progend(void);
static void segment(int);
static void space(int);
static void target(Node);
static void clobber(Node);
static Symbol rmap(int);
static void blkfetch(int, int, int, int);
static void blkstore(int, int, int, int);
static void blkloop(int, int, int, int, int, int[]);

/* Globals */
static int cseg = 0;
static int offset = 0;
static int maxoffset = 0;

/* Register definitions */
static Symbol intreg[32];
static Symbol intregw;
#define IREG 1

%}

%start stmt

/* Minimal terminal set - add more as needed */
%term CNSTI1=1045 CNSTU1=1046
%term CNSTI4=4117 CNSTU4=4118
%term ASGNI1=1077 ASGNU1=1078
%term INDIRI1=1093 INDIRU1=1094
%term ADDRLP2=2343 ADDRFP2=2327 ADDRGP2=2311
%term ADDI1=1333 SUBI1=1349
%term LOADI1=1253 LOADU1=1254
%term RETI1=1269 RETU1=1270 RETV=248
%term LABELV=600 JUMPV=584
%term CALLV=216 CALLI1=1237
%term ARGI1=1061

%%

/* Virtual register rules (required) */
reg: INDIRI1(VREGP)  "# vreg\n"
reg: INDIRU1(VREGP)  "# vreg\n"
stmt: ASGNI1(VREGP,reg)  "# vreg\n"
stmt: ASGNU1(VREGP,reg)  "# vreg\n"

/* Constants */
con: CNSTI1  "%a"
con: CNSTU1  "%a"
reg: con  "    LDI %0\n"  1

/* Addresses */
addr: ADDRLP2  "%a"
addr: ADDRFP2  "%a"
addr: ADDRGP2  "%a"

/* Load from memory */
reg: INDIRI1(addr)  "    LDA %0\n"  2
reg: INDIRU1(addr)  "    LDA %0\n"  2

/* Store to memory */
stmt: ASGNI1(addr,reg)  "    STA %0\n"  2
stmt: ASGNU1(addr,reg)  "    STA %0\n"  2

/* Arithmetic */
reg: ADDI1(reg,reg)  "    ; add\n    TAX\n    POP\n    ADDX\n"  4
reg: SUBI1(reg,reg)  "    ; sub\n    TAX\n    POP\n    SUBX\n"  4

/* Register loads */
reg: LOADI1(reg)  ""  1
reg: LOADU1(reg)  ""  1

/* Control flow */
stmt: LABELV  "%a:\n"
stmt: JUMPV(addr)  "    JMP %0\n"  1

/* Function calls */
stmt: ARGI1(reg)  "    PUSH\n"  1
reg: CALLI1(addr)  "    CALL %0\n"  3
stmt: CALLV(addr)  "    CALL %0\n"  3

/* Returns */
stmt: RETI1(reg)  "# ret\n"  0
stmt: RETU1(reg)  "# ret\n"  0
stmt: RETV  "# ret\n"  0

/* Catch-all */
stmt: reg  ""

%%

/* Implementation of interface functions */

static void progbeg(int argc, char *argv[]) {
    int i;

    /* Initialize register */
    intreg[0] = mkreg("AC", 0, 1, IREG);
    intregw = mkwildcard(intreg);

    /* Set register masks */
    tmask[IREG] = 0x01;
    vmask[IREG] = 0;

    /* Emit header */
    print("; Generated by LCC\n\n");
}

static void progend(void) {
    print("\n    HLT\n");
}

static void segment(int s) {
    if (cseg != s) {
        cseg = s;
        switch (s) {
        case CODE: print("\n    .text\n"); break;
        case DATA: print("\n    .data\n"); break;
        case BSS:  print("\n    .bss\n"); break;
        case LIT:  print("\n    .rodata\n"); break;
        }
    }
}

static void defsymbol(Symbol p) {
    if (p->x.name == NULL) {
        if (p->scope >= LOCAL && p->sclass == STATIC)
            p->x.name = stringf("L%d", genlabel(1));
        else if (p->generated)
            p->x.name = stringf("L%s", p->name);
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

static void defconst(int suffix, int size, Value v) {
    switch (size) {
    case 1: print("    .byte %d\n", v.u & 0xFF); break;
    case 2: print("    .word %d\n", v.u & 0xFFFF); break;
    case 4: print("    .long %d\n", v.u); break;
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

static void local(Symbol p) {
    offset = roundup(offset + p->type->size, p->type->align);
    p->x.offset = -offset;
    p->x.name = stringf("%d", -offset);
}

static void function(Symbol f, Symbol caller[], Symbol callee[], int ncalls) {
    int i;

    print("\n%s:\n", f->x.name);
    print("    ; prologue\n");
    print("    PUSH_FP\n");
    print("    TSF\n");

    usedmask[IREG] = 0;
    freemask[IREG] = tmask[IREG];

    /* Set up parameter offsets */
    for (i = 0; callee[i]; i++) {
        Symbol p = callee[i];
        Symbol q = caller[i];
        p->x.offset = q->x.offset = 4 + i;
        p->x.name = q->x.name = stringf("%d", 4 + i);
        p->sclass = q->sclass = AUTO;
    }

    offset = maxoffset = 0;
    gencode(caller, callee);

    /* Allocate locals */
    if (maxoffset > 0) {
        for (i = 0; i < maxoffset; i++) {
            print("    LDI 0\n");
            print("    PUSH\n");
        }
    }

    emitcode();

    print("    ; epilogue\n");
    print("    TFS\n");
    print("    POP_FP\n");
    print("    RET\n");
}

static void blockbeg(Env *e) {
    e->offset = offset;
}

static void blockend(Env *e) {
    if (offset > maxoffset)
        maxoffset = offset;
    offset = e->offset;
}

static Symbol rmap(int opk) {
    return intregw;
}

static void target(Node p) {
    switch (specific(p->op)) {
    case CALL+I:
    case CALL+U:
    case CALL+V:
        setreg(p, intreg[0]);
        break;
    case RET+I:
    case RET+U:
        rtarget(p, 0, intreg[0]);
        break;
    }
}

static void clobber(Node p) {
    switch (specific(p->op)) {
    case CALL+I:
    case CALL+U:
    case CALL+V:
        spill(0xFF, IREG, p);
        break;
    }
}

static void emit2(Node p) { }
static void doarg(Node p) { }
static void blkfetch(int k, int off, int reg, int tmp) { }
static void blkstore(int k, int off, int reg, int tmp) { }
static void blkloop(int dreg, int doff, int sreg, int soff, int size, int tmps[]) { }

Interface mytargetIR = {
    1, 1, 0,  /* char */
    1, 1, 0,  /* short */
    1, 1, 0,  /* int */
    2, 1, 0,  /* long */
    2, 1, 0,  /* long long */
    0, 1, 1,  /* float */
    0, 1, 1,  /* double */
    0, 1, 1,  /* long double */
    2, 1, 0,  /* pointer */
    0, 1, 0,  /* struct */
    1,        /* little_endian */
    0,        /* mulops_calls */
    0,        /* wants_callb */
    1,        /* wants_argb */
    0,        /* left_to_right */
    0,        /* wants_dag */
    1,        /* unsigned_char */
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
    0, 0, 0, 0, 0, 0, 0,
    {
        1,
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

### Step 3: Update the Makefile

Add to the makefile:

```makefile
# Add to RCCOBJS
RCCOBJS=$Balloc$O ... $Bmytarget$O

# Add lburg rule
$Bmytarget.c: $Blburg$E src/mytarget.md
	$Blburg src/mytarget.md $@

# Add compilation rule
$Bmytarget$O: $Bmytarget.c
	$(CC) $(CFLAGS) -c -Isrc -o $@ $Bmytarget.c
```

### Step 4: Build and Test

```bash
# Clean and rebuild
make clean
make BUILDDIR=build

# Test with a simple program
echo 'char main(void) { return 42; }' > test.c
./build/rcc -target=mytarget test.c
```

---

## Terminal Definitions: Complete Reference

### Calculating Terminal Numbers

Formula: `terminal = size * 1024 + op * 16 + type + 5`

### Operation Numbers (from ops.h)

| Op | Number | Description |
|----|--------|-------------|
| CNST | 1 | Constant |
| ARG | 2 | Function argument |
| ASGN | 3 | Assignment |
| INDIR | 4 | Load from memory |
| CVC | 5 | Char conversion |
| CVD | 6 | Double conversion |
| CVF | 7 | Float conversion |
| CVI | 8 | Int conversion |
| CVP | 9 | Pointer conversion |
| CVS | 10 | Short conversion |
| CVU | 11 | Unsigned conversion |
| NEG | 12 | Negation |
| CALL | 13 | Function call |
| LOAD | 14 | Register load |
| RET | 15 | Return |
| ADDRG | 16 | Address of global |
| ADDRF | 17 | Address of formal |
| ADDRL | 18 | Address of local |
| ADD | 19 | Addition |
| SUB | 20 | Subtraction |
| LSH | 21 | Left shift |
| MOD | 22 | Modulo |
| RSH | 23 | Right shift |
| BAND | 24 | Bitwise AND |
| BCOM | 25 | Bitwise complement |
| BOR | 26 | Bitwise OR |
| BXOR | 27 | Bitwise XOR |
| DIV | 28 | Division |
| MUL | 29 | Multiplication |
| EQ | 30 | Equal |
| GE | 31 | Greater or equal |
| GT | 32 | Greater than |
| LE | 33 | Less or equal |
| LT | 34 | Less than |
| NE | 35 | Not equal |
| JUMP | 36 | Unconditional jump |
| LABEL | 37 | Label definition |
| VREG | 44 | Virtual register |

### Type Codes

| Type | Code | Description |
|------|------|-------------|
| I | 0 | Signed integer |
| U | 1 | Unsigned integer |
| P | 2 | Pointer |
| V | 3 | Void |
| B | 4 | Block/struct |
| F | 5 | Float |

### Common Terminal Reference Table

| Terminal | Number | Calculation |
|----------|--------|-------------|
| CNSTI1 | 1045 | 1*1024 + 1*16 + 0 + 5 |
| CNSTU1 | 1046 | 1*1024 + 1*16 + 1 + 5 |
| CNSTI2 | 2069 | 2*1024 + 1*16 + 0 + 5 |
| CNSTI4 | 4117 | 4*1024 + 1*16 + 0 + 5 |
| ARGI1 | 1061 | 1*1024 + 2*16 + 0 + 5 |
| ASGNI1 | 1077 | 1*1024 + 3*16 + 0 + 5 |
| ASGNU1 | 1078 | 1*1024 + 3*16 + 1 + 5 |
| INDIRI1 | 1093 | 1*1024 + 4*16 + 0 + 5 |
| INDIRU1 | 1094 | 1*1024 + 4*16 + 1 + 5 |
| LOADI1 | 1253 | 1*1024 + 14*16 + 0 + 5 |
| LOADU1 | 1254 | 1*1024 + 14*16 + 1 + 5 |
| RETI1 | 1269 | 1*1024 + 15*16 + 0 + 5 |
| ADDRGP2 | 2311 | 2*1024 + 16*16 + 2 + 5 |
| ADDRFP2 | 2327 | 2*1024 + 17*16 + 2 + 5 |
| ADDRLP2 | 2343 | 2*1024 + 18*16 + 2 + 5 |
| ADDI1 | 1333 | 1*1024 + 19*16 + 0 + 5 |
| SUBI1 | 1349 | 1*1024 + 20*16 + 0 + 5 |
| MULI1 | 1493 | 1*1024 + 29*16 + 0 + 5 |
| DIVI1 | 1477 | 1*1024 + 28*16 + 0 + 5 |
| EQI1 | 1509 | 1*1024 + 30*16 + 0 + 5 |
| NEI1 | 1589 | 1*1024 + 35*16 + 0 + 5 |
| LTI1 | 1573 | 1*1024 + 34*16 + 0 + 5 |
| GTI1 | 1541 | 1*1024 + 32*16 + 0 + 5 |
| ADDP2 | 2359 | 2*1024 + 19*16 + 2 + 5 |
| JUMPV | 584 | 0*1024 + 36*16 + 3 + 5 |
| LABELV | 600 | 0*1024 + 37*16 + 3 + 5 |
| CALLV | 216 | 0*1024 + 13*16 + 3 + 5 |
| RETV | 248 | 0*1024 + 15*16 + 3 + 5 |
| VREGP | 711 | Special encoding |

---

## Writing Grammar Rules

### Rule Categories

#### 1. Virtual Register Rules (Required)

```c
reg: INDIRI1(VREGP)  "# vreg\n"
reg: INDIRU1(VREGP)  "# vreg\n"
stmt: ASGNI1(VREGP,reg)  "# vreg\n"
stmt: ASGNU1(VREGP,reg)  "# vreg\n"
```

These handle LCC's virtual register mechanism. The templates are just comments.

#### 2. Constant Rules

```c
/* Constant nonterminals */
con1: CNSTI1  "%a"
con1: CNSTU1  "%a"
con2: CNSTI2  "%a"
con4: CNSTI4  "%a"

/* Load constant into register */
reg: con1  "    LDI %0\n"  1
reg: con4  "    LDI %0\n"  1  /* Truncate to CPU width */
```

#### 3. Address Rules

```c
addr: ADDRGP2  "%a"    /* Global */
addr: ADDRFP2  "%a"    /* Parameter */
addr: ADDRLP2  "%a"    /* Local */

/* For frame-pointer relative addressing */
addr: ADDRFP2  "%a,FP"  /* Parameter at offset,FP */
addr: ADDRLP2  "%a,FP"  /* Local at offset,FP */
```

#### 4. Memory Access Rules

```c
/* Load */
reg: INDIRI1(addr)  "    LDA %0\n"  2
reg: INDIRU1(addr)  "    LDA %0\n"  2

/* Store */
stmt: ASGNI1(addr,reg)  "    STA %0\n"  2
stmt: ASGNU1(addr,reg)  "    STA %0\n"  2

/* With LOAD wrappers (critical!) */
reg: LOADI1(reg)  ""  1
reg: LOADU1(reg)  ""  1
```

#### 5. Arithmetic Rules

```c
/* Addition */
reg: ADDI1(reg,reg)  "    TAX\n    POP\n    ADDX\n"  3

/* With memory operand (more efficient) */
reg: ADDI1(LOADI1(INDIRU1(addr)),LOADI1(INDIRU1(addr)))  "    LDA %0\n    ADD %1\n"  2

/* Subtraction - careful with operand order! */
reg: SUBI1(reg,reg)  "    TAX\n    POP\n    STA _t\n    TXA\n    STA _t2\n    LDA _t\n    SUB _t2\n"  7

/* With memory operand */
reg: SUBI1(LOADI1(INDIRU1(addr)),LOADI1(INDIRU1(addr)))  "    LDA %0\n    SUB %1\n"  2

/* Increment/Decrement (special case for +1/-1) */
conN: CNSTI1  "%a"  range(a, 1, 1)
reg: ADDI1(reg,conN)  "    INC\n"  1
reg: SUBI1(reg,conN)  "    DEC\n"  1

/* Multiply and Divide */
reg: MULI1(reg,reg)  "    TAX\n    POP\n    MUL\n"  3
reg: DIVI1(reg,reg)  "    TAX\n    POP\n    DIV\n"  3
```

#### 6. Comparison and Jump Rules

```c
/* Labels */
stmt: LABELV  "%a:\n"

/* Unconditional jump */
stmt: JUMPV(addr)  "    JMP %0\n"  1

/* Comparisons - emit compare + conditional jump */
stmt: EQI1(reg,reg)  "    TAX\n    POP\n    CMP X\n    JZ %a\n"  4
stmt: NEI1(reg,reg)  "    TAX\n    POP\n    CMP X\n    JNZ %a\n"  4
stmt: LTI1(reg,reg)  "    TAX\n    POP\n    CMP X\n    JLT %a\n"  4
stmt: GTI1(reg,reg)  "    TAX\n    POP\n    CMP X\n    JGT %a\n"  4

/* Optimized: compare with memory */
stmt: EQI1(reg,LOADI1(INDIRU1(addr)))  "    CMP %1\n    JZ %a\n"  3
```

#### 7. Function Call Rules

```c
/* Push arguments */
stmt: ARGI1(reg)  "    PUSH\n"  1

/* Call functions */
reg: CALLI1(addr)  "    CALL %0\n"  3
stmt: CALLV(addr)  "    CALL %0\n"  3

/* Returns */
stmt: RETI1(reg)  "# ret\n"  0
stmt: RETU1(reg)  "# ret\n"  0
stmt: RETV  "# ret\n"  0
```

#### 8. Type Conversion Rules

```c
/* Truncation (larger to smaller) */
reg: CVII1(reg)  "# truncate\n"  0
reg: CVUI1(reg)  "# truncate\n"  0

/* Extension (smaller to larger) */
reg: CVII4(reg)  "# extend\n"  0
reg: CVIU4(reg)  "# extend\n"  0
```

#### 9. Pointer Arithmetic Rules

```c
%term ADDP2=2359

/* Pointer addition for array indexing */
addr: ADDP2(addr,reg)  "%0"  1
reg: ADDP2(reg,reg)  "    ; ptr add\n"  2

/* Indexed load/store */
reg: INDIRU1(ADDP2(addr,reg))  "    TAX\n    LDA %0,X\n"  3
stmt: ASGNU1(ADDP2(addr,reg),reg)  "    TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n"  5

/* Handle reversed operand order */
reg: INDIRU1(ADDP2(reg,addr))  "    TAX\n    LDA %1,X\n"  3
stmt: ASGNU1(ADDP2(reg,addr),reg)  "    TAY\n    POP\n    TAX\n    TYA\n    STA %1,X\n"  5
```

### Common Rule Patterns

**Pattern 1: Binary operation with stack**
```
Right operand computed → save to temp → pop left → operate
```

**Pattern 2: Combine load with operation**
```
Instead of: LDA a; TAX; LDA b; ADDX
Use:        LDA a; ADD b
```

**Pattern 3: Special cases for small constants**
```
Use INC/DEC instead of ADD 1/SUB 1
```

---

## Implementing Interface Functions

### Required Functions

| Function | Purpose |
|----------|---------|
| `progbeg` | Called at start of compilation |
| `progend` | Called at end of compilation |
| `segment` | Switch output segment |
| `defsymbol` | Define a symbol's assembly name |
| `address` | Create address expression |
| `defconst` | Emit constant data |
| `defaddress` | Emit address data |
| `defstring` | Emit string data |
| `space` | Emit uninitialized space |
| `export` | Export symbol |
| `import` | Import external symbol |
| `global` | Define global label |
| `local` | Handle local variable |
| `function` | Generate function prologue/epilogue |
| `blockbeg` | Start of block scope |
| `blockend` | End of block scope |
| `emit` | Emit a node (generated by lburg) |
| `gen` | Generate code (generated by lburg) |
| `rmap` | Map operation to register class |
| `target` | Set register targets |
| `clobber` | Declare clobbered registers |

### Function Implementations

```c
/* Program start */
static void progbeg(int argc, char *argv[]) {
    int i;

    /* Process arguments */
    for (i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-d") == 0)
            /* Enable debug mode */;
    }

    /* Initialize registers */
    intreg[0] = mkreg("AC", 0, 1, IREG);
    intregw = mkwildcard(intreg);

    tmask[IREG] = 0x01;  /* Available registers */
    vmask[IREG] = 0;     /* Volatile (caller-saved) */

    /* Emit file header */
    print("; Generated by LCC\n");
    print("    .org 0x0100\n\n");
}

/* Program end */
static void progend(void) {
    print("\n    HLT\n");
}

/* Segment switching */
static void segment(int s) {
    if (cseg == s) return;
    cseg = s;
    switch (s) {
    case CODE: print("\n    .text\n"); break;
    case DATA: print("\n    .data\n"); break;
    case BSS:  print("\n    .bss\n"); break;
    case LIT:  print("\n    .rodata\n"); break;
    }
}

/* Symbol naming */
static void defsymbol(Symbol p) {
    if (p->x.name == NULL) {
        if (p->scope >= LOCAL && p->sclass == STATIC)
            p->x.name = stringf("L%d", genlabel(1));
        else if (p->generated)
            p->x.name = stringf("L%s", p->name);
        else if (p->scope == GLOBAL || p->sclass == EXTERN)
            p->x.name = stringf("_%s", p->name);
        else
            p->x.name = p->name;
    }
}

/* Address computation */
static void address(Symbol q, Symbol p, long n) {
    if (p->scope == GLOBAL || p->sclass == STATIC || p->sclass == EXTERN)
        q->x.name = stringf("%s%s%D", p->x.name, n >= 0 ? "+" : "", n);
    else {
        q->x.offset = p->x.offset + n;
        q->x.name = stringf("%d", q->x.offset);
    }
}

/* Function code generation */
static void function(Symbol f, Symbol caller[], Symbol callee[], int ncalls) {
    int i, param_offset;

    /* Function label */
    print("\n; Function %s\n", f->name);
    print("%s:\n", f->x.name);

    /* Prologue */
    print("    PUSH_FP\n");
    print("    TSF\n");  /* FP = SP */

    /* Initialize register allocator */
    usedmask[IREG] = 0;
    freemask[IREG] = tmask[IREG];

    /* Parameter offsets */
    param_offset = 4;  /* Skip saved FP and return address */
    for (i = 0; callee[i]; i++) {
        Symbol p = callee[i];
        Symbol q = caller[i];
        p->x.offset = q->x.offset = param_offset;
        p->x.name = q->x.name = stringf("%d", param_offset);
        p->sclass = q->sclass = AUTO;
        param_offset += roundup(q->type->size, 1);
    }

    /* Generate code */
    offset = maxoffset = 0;
    gencode(caller, callee);

    /* Allocate locals */
    if (maxoffset > 0) {
        print("    ; Allocate %d locals\n", maxoffset);
        for (i = 0; i < maxoffset; i++) {
            print("    LDI 0\n");
            print("    PUSH\n");
        }
    }

    /* Emit generated code */
    emitcode();

    /* Epilogue */
    print("    TFS\n");    /* SP = FP */
    print("    POP_FP\n");
    print("    RET\n");
}

/* Block scope management */
static void blockbeg(Env *e) {
    e->offset = offset;
}

static void blockend(Env *e) {
    if (offset > maxoffset)
        maxoffset = offset;
    offset = e->offset;
}

/* Local variable allocation */
static void local(Symbol p) {
    offset = roundup(offset + p->type->size, p->type->align);
    p->x.offset = -offset;
    p->x.name = stringf("%d", -offset);
}

/* Register mapping */
static Symbol rmap(int opk) {
    return intregw;
}

/* Register targeting for calls and returns */
static void target(Node p) {
    switch (specific(p->op)) {
    case CALL+I:
    case CALL+U:
    case CALL+P:
    case CALL+V:
        setreg(p, intreg[0]);
        break;
    case RET+I:
    case RET+U:
        rtarget(p, 0, intreg[0]);
        break;
    }
}

/* Register clobbering */
static void clobber(Node p) {
    switch (specific(p->op)) {
    case CALL+I:
    case CALL+U:
    case CALL+P:
    case CALL+V:
        spill(0xFF, IREG, p);
        break;
    }
}
```

---

## Register Allocation and Management

### Register Classes

LCC organizes registers into classes. For simple CPUs, one class is usually enough:

```c
#define IREG 1  /* Integer register class */

static Symbol intreg[32];  /* Register symbols */
static Symbol intregw;     /* Wildcard for the class */
```

### Initializing Registers

```c
static void progbeg(int argc, char *argv[]) {
    /* Create register symbols */
    intreg[0] = mkreg("AC", 0, 1, IREG);  /* Accumulator */
    intreg[1] = mkreg("X", 1, 1, IREG);   /* Index X (if usable) */
    intreg[2] = mkreg("Y", 2, 1, IREG);   /* Index Y (if usable) */

    /* Create wildcard (represents any register in class) */
    intregw = mkwildcard(intreg);

    /* Set available registers mask */
    tmask[IREG] = 0x07;  /* Registers 0, 1, 2 available */

    /* Set volatile (caller-saved) registers */
    vmask[IREG] = 0x07;  /* All are caller-saved */
}
```

### Register Masks

| Mask | Purpose |
|------|---------|
| `tmask[class]` | Allocatable registers |
| `vmask[class]` | Volatile (caller-saved) registers |
| `usedmask[class]` | Used in current function |
| `freemask[class]` | Currently free registers |

### For Accumulator-Only Architectures

If your CPU has only one register (accumulator), you still need proper initialization:

```c
static void progbeg(int argc, char *argv[]) {
    /* Single accumulator */
    intreg[0] = mkreg("AC", 0, 1, IREG);
    intregw = mkwildcard(intreg);

    tmask[IREG] = 0x01;  /* Only register 0 */
    vmask[IREG] = 0x01;  /* It's volatile */
}

static Symbol rmap(int opk) {
    return intregw;  /* All operations use AC */
}
```

---

## Calling Conventions Design

### Stack Frame Layout

Design your stack frame carefully:

```
High Address
┌──────────────────┐
│    Argument N    │ [FP + 4 + (N-1)]
│       ...        │
│    Argument 1    │ [FP + 4]
├──────────────────┤
│  Return Address  │ [FP + 2] (2 bytes for 16-bit addr)
├──────────────────┤
│    Saved FP      │ [FP + 0] (2 bytes)
├──────────────────┤ ← FP points here
│    Local 1       │ [FP - 1]
│    Local 2       │ [FP - 2]
│       ...        │
├──────────────────┤ ← SP points here
Low Address
```

### Calling Sequence

**Caller (before call):**
```assembly
    ; Push arguments right-to-left
    LDA arg2
    PUSH
    LDA arg1
    PUSH
    ; Call function
    CALL _function
    ; Clean up stack (caller cleans)
    POP     ; Remove arg1
    POP     ; Remove arg2
    ; Result is in AC
```

**Callee (function body):**
```assembly
_function:
    ; Prologue
    PUSH_FP         ; Save caller's FP
    TSF             ; FP = SP

    ; Allocate locals (optional)
    LDI 0
    PUSH            ; Local variable space

    ; Access parameters
    LDA 4,FP        ; First parameter
    LDA 5,FP        ; Second parameter

    ; Access locals
    STA -1,FP       ; First local

    ; ... function body ...

    ; Epilogue
    LDA -1,FP       ; Return value in AC
    TFS             ; SP = FP (deallocate locals)
    POP_FP          ; Restore caller's FP
    RET             ; Return
```

### Return Values

| Size | Location |
|------|----------|
| 1 byte | AC |
| 2 bytes | Y:AC (high:low) |
| Struct | Pointer in AC |

---

## Building and Compiling

### Build Commands

```bash
# Full clean build
make clean
make BUILDDIR=build

# Just rebuild the backend after changes
rm build/mytarget.c build/mytarget.o
make BUILDDIR=build

# Quick rebuild (if only .md changed)
./build/lburg src/mytarget.md build/mytarget.c
$(CC) -c -Isrc -o build/mytarget.o build/mytarget.c
# Then relink rcc
```

### Using the Compiler

```bash
# Compile C to assembly
./build/rcc -target=mytarget program.c > program.asm

# With preprocessor
cpp program.c | ./build/rcc -target=mytarget > program.asm

# See IR before instruction selection
./build/rcc -target=symbolic program.c
```

### Common Build Errors

| Error | Cause | Solution |
|-------|-------|----------|
| `undefined reference to mytargetIR` | Not registered in bind.c | Add to xx/yy list |
| `missing include` | Wrong include path | Add `-Isrc` to compile |
| `lburg errors` | Syntax error in .md | Check rule syntax |

---

## Debugging Your Backend

### Enable Debug Output

In `src/gen.c`, temporarily enable:

```c
int dflag = 1;  /* Change from 0 to 1 */
```

This produces output showing the actual IR trees:

```
dumpcover: n=0x... ADDI1
  l=0x... LOADI1
    l=0x... INDIRU1
      l=0x... ADDRLP2
  r=0x... LOADI1
    ...
```

### Use the Symbolic Backend

```bash
./build/rcc -target=symbolic test.c
```

Shows the IR without instruction selection, helping identify needed terminals.

### Common Debug Techniques

**1. Trace rule selection:**

After building, examine the generated C file:
```bash
grep "_rule\[" build/mytarget.c | head -20
```

**2. Check terminal numbers:**

Verify your terminal calculations match LCC's encoding.

**3. Add print statements:**

In interface functions:
```c
static void function(...) {
    print("; DEBUG: entering function %s\n", f->name);
    /* ... */
}
```

**4. Use GDB/LLDB:**

```bash
lldb -- ./build/rcc -target=mytarget test.c
(lldb) run
(lldb) bt  # Backtrace on crash
```

### Understanding Error Messages

| Error | Meaning | Fix |
|-------|---------|-----|
| `Bad terminal XXXX` | Missing terminal/rule | Add %term and rule |
| `Bad goal nonterminal 0` | Empty template for instruction | Use `"# comment\n"` |
| `can't find a reg` | Register allocator failed | Check rmap, masks |
| `corrupt XXXX node` | Invalid IR tree | Check rule patterns |

---

## Testing Strategies

### Progressive Test Suite

**Level 1: Minimal (return constant)**
```c
char main(void) { return 42; }
```

**Level 2: Variables**
```c
char main(void) { char x = 5; return x; }
```

**Level 3: Parameters**
```c
char id(char x) { return x; }
char main(void) { return id(7); }
```

**Level 4: Arithmetic**
```c
char add(char a, char b) { return a + b; }
char main(void) { return add(3, 5); }
```

**Level 5: Conditionals**
```c
char max(char a, char b) {
    if (a > b) return a;
    return b;
}
```

**Level 6: Loops**
```c
char sum(void) {
    char i = 0, s = 0;
    while (i < 10) {
        s = s + i;
        i = i + 1;
    }
    return s;
}
```

**Level 7: Arrays (constant index)**
```c
char arr[3];
char main(void) {
    arr[0] = 1;
    arr[1] = 2;
    return arr[0] + arr[1];
}
```

**Level 8: Arrays (variable index)**
```c
char arr[5];
char main(void) {
    char i = 2;
    arr[i] = 42;
    return arr[i];
}
```

**Level 9: Pointers**
```c
char x;
char main(void) {
    char *p = &x;
    *p = 42;
    return x;
}
```

**Level 10: Complex expressions**
```c
char main(void) {
    char a = 3, b = 4, c = 5;
    return (a + b) * c - (a * b);
}
```

### Automated Testing

```bash
#!/bin/bash
# test_backend.sh

COMPILER="./build/rcc -target=mytarget"
TESTS="test1.c test2.c test3.c"

for test in $TESTS; do
    echo "Testing $test..."
    if $COMPILER $test > /dev/null 2>&1; then
        echo "  PASS"
    else
        echo "  FAIL"
    fi
done
```

### Comparing Outputs

```bash
# Generate reference output
./build/rcc -target=x86linux test.c > test.x86.s

# Generate your output
./build/rcc -target=mytarget test.c > test.my.s

# Compare structure (ignoring specific instructions)
diff -u <(grep -E '^\s+[a-zA-Z]' test.x86.s) \
        <(grep -E '^\s+[a-zA-Z]' test.my.s)
```

---

## Advanced Topics

### Multi-Byte Operations

For 8-bit CPUs handling 16-bit or 32-bit values:

```c
/* 16-bit addition using 8-bit ops with carry */
reg: ADDI2(reg,reg)  "    ; 16-bit add\n    LDA %0_lo\n    ADD %1_lo\n    STA _res_lo\n    LDA %0_hi\n    ADC %1_hi\n    STA _res_hi\n"  10
```

### Floating Point

Most 8/16-bit CPUs use software floating point:

```c
/* In Interface: */
0, 1, 1,  /* float - size=0, align=1, outofline=1 (not supported inline) */

/* Calls to runtime library */
reg: ADDF4(reg,reg)  "    CALL __addf\n"  100
```

### Optimizations

**Peephole optimization example:**
```c
/* Combine load-store to move */
reg: LOADI1(INDIRI1(addr))  "    ; peephole: skip redundant load\n"  0
```

**Strength reduction:**
```c
/* Multiply by 2 -> shift */
con2: CNSTI1  "%a"  range(a, 2, 2)
reg: MULI1(reg,con2)  "    SHL\n"  1
```

### Position-Independent Code

```c
/* For PIC, use PC-relative addressing */
addr: ADDRGP2  "%a-.\n"  /* Offset from current PC */
```

---

## Troubleshooting Guide

### Problem: "Bad terminal XXXX"

**Steps:**
1. Calculate what terminal XXXX represents
2. Add `%term NAME=XXXX` to your .md file
3. Add a grammar rule for it

**Example:** Terminal 2359
- 2359 = 2*1024 + 19*16 + 2 + 5 = ADDP2 (pointer add)
- Add: `%term ADDP2=2359`
- Add: `addr: ADDP2(addr,reg)  "%0"  1`

### Problem: Wrong code generated

**Steps:**
1. Enable dflag in gen.c
2. Look at actual tree structure
3. Check if LOAD nodes are present
4. Add rules matching actual tree

**Example:** Expected `LDA a; ADD b` but got `LDA a; LDA b; ADDX`
- Actual tree has LOAD wrappers
- Add: `reg: ADDI1(LOADI1(INDIRU1(addr)),LOADI1(INDIRU1(addr)))`

### Problem: Infinite loop during compilation

**Steps:**
1. Check for missing conversion rules (CVII, CVUI, etc.)
2. Check for missing LOAD rules
3. Ensure all paths lead to `stmt`

### Problem: Register allocation fails

**Steps:**
1. Verify `mkreg` uses array, not single pointer
2. Check `tmask` is set correctly
3. Verify `rmap` returns correct wildcard

### Problem: Function calls don't work

**Steps:**
1. Check `target()` sets return register
2. Check `clobber()` spills registers
3. Verify stack frame layout
4. Check parameter offset calculations

### Problem: Array access fails

**Steps:**
1. Add ADDP2 terminal and rules
2. Handle both operand orderings
3. Add CVUU2 for index conversion

---

## Complete Example: 8-bit CPU Backend

Here's a complete, minimal backend for an 8-bit accumulator-based CPU:

See [PORTING_NEANDER.md](PORTING_NEANDER.md) for a fully worked example with the NEANDER-X processor.

Key takeaways from that example:

1. **Start minimal**: Begin with return constants, add features incrementally
2. **Watch for LOAD nodes**: IR trees have LOAD wrappers you must match
3. **Handle unsigned_char**: Affects which terminals are generated
4. **Both operand orders**: `ADDP2(addr,reg)` AND `ADDP2(reg,addr)`
5. **Use dflag**: Essential for understanding actual tree structure

---

## References and Resources

### Official Documentation

- **LCC GitHub**: https://github.com/drh/lcc
- **LCC Website**: https://drh.github.io/lcc/
- **Interface Documentation**: https://drh.github.io/lcc/documents/interface4.pdf
- **Installation Guide**: LCC doc/install.html

### Books

- **A Retargetable C Compiler: Design and Implementation** by Fraser & Hanson (ISBN 0-8053-1670-1) - The definitive LCC reference

### Tutorials

- **Retargeting LCC for Magic-1**: https://www.homebrewcpu.com/retargeting_lcc.htm
- **This document** and PORTING_NEANDER.md

### Community

- **comp.compilers.lcc**: USENET newsgroup
- **GitHub Issues**: For LCC bugs and questions

### Related Projects

- **SDCC**: Small Device C Compiler (alternative for 8-bit)
- **CC65**: C compiler for 6502
- **Z88DK**: C compiler for Z80

---

## Appendix A: Quick Reference Card

### Terminal Formula
```
terminal = size * 1024 + op * 16 + type + 5
```

### Common Terminals
```
CNSTI1=1045  ADDI1=1333  INDIRI1=1093  ASGNI1=1077
CNSTU1=1046  SUBI1=1349  INDIRU1=1094  ASGNU1=1078
LOADI1=1253  MULI1=1493  ADDRLP2=2343  ADDP2=2359
LOADU1=1254  DIVI1=1477  ADDRFP2=2327  LABELV=600
RETI1=1269   EQI1=1509   ADDRGP2=2311  JUMPV=584
```

### Rule Template
```
nonterminal: PATTERN(children)  "assembly template"  cost
```

### Template Markers
```
%a  - symbol name
%0  - first child result
%1  - second child result
%c  - register name
%%  - literal %
```

### Interface Flags
```
little_endian  - byte order
unsigned_char  - char signedness
mulops_calls   - MUL/DIV are calls
wants_argb     - push struct args
```

---

*This tutorial is part of the NEANDER-X Educational Processor Project.*
