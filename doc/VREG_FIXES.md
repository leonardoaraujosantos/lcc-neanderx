# LCC Neander-X Backend: VREG and Code Generation Fixes

## Overview

This document describes the fixes made to the LCC compiler backend for the Neander-X 16-bit CPU, specifically addressing issues with Virtual Register (VREG) handling and binary operation code generation.

## Problems Identified and Solved

### 1. VREG Spill from Frame Address (SOLVED)

**Problem**: When a function parameter or local variable needed to be spilled to a VREG (e.g., `x + x` where `x` is used twice), the generated code was missing the load instruction before storing to the VREG.

**Example of broken code** (for `double_val(int x) { return x + x; }`):
```asm
_double_val:
    PUSH_FP
    TSF
    LDI 0
    PUSH
    STA _vreg0      ; Missing LDA 4,FP before this!
    LDA _vreg0
    STA _tmp
    LDA _vreg0
    ADD _tmp
```

**Root Cause**: The `emit2()` callback function was supposed to handle VREG writes, but it wasn't loading the source value first when the source was an INDIRI2 from a frame address (ADDRFP2/ADDRLP2).

**Solution**: Modified `emit2()` to detect when the ASGN operation's right child is an INDIRI2 with an address operand (ADDRF, ADDRL, ADDRG) and emit the appropriate LDA instruction before the STA to the VREG slot.

```c
case ASGN+I:
case ASGN+U:
case ASGN+P:
    if (IS_VREG_NODE(LEFT_CHILD(p))) {
        // ... get vreg slot ...
        right = RIGHT_CHILD(p);
        if (right && generic(right->op) == INDIR) {
            Node addr = LEFT_CHILD(right);
            if (generic(addr->op) == ADDRF) {
                print("    LDA %d,FP\n", addr->syms[0]->x.offset);
            } else if (generic(addr->op) == ADDRL) {
                print("    LDA %d,FP\n", addr->syms[0]->x.offset);
            } else if (generic(addr->op) == ADDRG) {
                print("    LDA %s\n", addr->syms[0]->x.name);
            }
        }
        print("    STA _vreg%d\n", slot);
    }
    break;
```

### 2. Binary Operation (reg,reg) Rules Missing Child Emission (SOLVED)

**Problem**: Rules like `BXORI2(reg,reg)`, `BORI2(reg,reg)`, `ADDI2(reg,reg)` had templates that didn't emit their children using `%0` and `%1`, causing incorrect code generation when operands were VREGs.

**Example of broken template**:
```
reg: BXORI2(reg,reg)  "    STA _tmp\n    POP\n    XOR _tmp\n"  10
```

This template assumed one operand was on the stack (POP), but children were being emitted separately by emit2() for VREG reads, causing both LDA instructions to be output before the parent's template, losing the first value.

**Solution**: Added `%0` and `%1` to templates to properly emit children in the correct order:

```
reg: BXORI2(reg,reg)  "%0    STA _tmp\n%1    XOR _tmp\n"  10
```

Fixed rules include:
- BANDI2, BANDU2 (AND operations)
- BORI2, BORU2 (OR operations)
- BXORI2, BXORU2 (XOR operations)
- ADDI2, ADDU2, ADDP2 (ADD operations)
- SUBI2, SUBU2 (SUB operations)
- MULI2, MULU2 (MUL operations)
- DIVI2, DIVU2 (DIV operations)
- MODI2, MODU2 (MOD operations)

## Difficulties Encountered

### 1. Understanding lburg Template Syntax

**Difficulty**: Figuring out that `%N` in lburg templates refers to the Nth *nonterminal* child, skipping terminals. For example, in `ASGNI2(VREGP, INDIRI2(faddr))`, VREGP is a terminal so `%0` refers to `faddr`, not VREGP.

**Resolution**: Traced through generated C code and lburg documentation to understand the numbering scheme.

### 2. emit2() Opcode Matching

**Difficulty**: The `specific(p->op)` function returns a value that should match `ASGN+I`, `INDIR+I`, etc., but debugging showed mismatches (e.g., `op=309` vs `ASGN+I=53`).

**Resolution**: The issue was that emit2() wasn't being called for certain patterns. When it was called, the opcodes did match correctly. The real issue was that templates starting with `#` call emit2() directly, but this happened for each child independently rather than coordinated with the parent.

### 3. Understanding LCC's Code Emission Flow

**Difficulty**: LCC's emitasm() function processes children only when the template contains `%N` references. Templates like `"# write vreg\n"` that start with `#` call emit2() directly but don't automatically emit children.

**Resolution**: This explained why changing templates to include `%0` and `%1` was necessary - without them, children weren't being emitted through the normal template mechanism.

### 4. VREG Global Memory Issue in Recursive Functions

**Difficulty**: Recursive functions like fibonacci fail because VREG slots are global memory locations (`_vreg0`, `_vreg1`, etc.) that get overwritten by nested calls.

**Current Status**: NOT FULLY SOLVED. This is an architectural limitation. Proper fix would require either:
- Stack-based spill slots instead of global memory
- Saving/restoring VREGs across function calls

## What Was Tried But Didn't Work

### 1. Specific Rules for VREG Assignment from faddr

**Approach**: Added rules like:
```
stmt: ASGNI2(VREGP, INDIRI2(faddr))  "    LDA %0\n; vreg from faddr\n"  0
```

**Result**: The template output appeared, but emit2() wasn't called for this specific rule pattern, so `STA _vreg0` was missing. The specific rule bypassed the generic rule's emit2() callback.

### 2. Using `%0` Alone in Generic VREG Write Rule

**Approach**: Changed generic rule to:
```
stmt: ASGNI2(VREGP,reg)  "%0"
```

**Result**: Caused "Bad goal nonterminal 0" error during compilation. The nts array wasn't set up correctly for this pattern.

### 3. Missing emit2() Handlers for SUB and Bitwise Operations (SOLVED)

**Problem**: The `emit2()` function had handlers for ADD (VREG + VREG) and MUL (VREG * VREG) operations, but was missing handlers for:
- SUB (VREG - VREG)
- BXOR (VREG ^ VREG)
- BAND (VREG & VREG)
- BOR (VREG | VREG)

This caused these operations to use the generic `(reg,reg)` rule which emits both VREG loads before the operation template, losing the first operand.

**Solution**: Added VREGP grammar rules and emit2() handlers for all missing operations:

```c
// Grammar rules added:
reg: SUBI2(INDIRI2(VREGP),INDIRI2(VREGP))  "# sub vreg-vreg\n"  3
reg: BXORI2(INDIRI2(VREGP),INDIRI2(VREGP))  "# xor vreg^vreg\n"  3
reg: BANDI2(INDIRI2(VREGP),INDIRI2(VREGP))  "# and vreg&vreg\n"  3
reg: BORI2(INDIRI2(VREGP),INDIRI2(VREGP))  "# or vreg|vreg\n"  3

// emit2() handler for SUB:
case SUB+I:
case SUB+U:
    if (vreg - vreg) {
        print("    LDA _vreg%d\n", slot2);  // subtrahend
        print("    STA _tmp\n");
        print("    LDA _vreg%d\n", slot1);  // minuend
        print("    SUB _tmp\n");
    }
    break;
```

### 4. Template %0 Prefix Causing Invalid Instructions (SOLVED)

**Problem**: Templates like `ADDI2(reg,INDIRI2(addr))` had `%0` at the start:
```
reg: ADDI2(reg,INDIRI2(addr))  "%0    STA _tmp\n    LDA %1\n    ADD _tmp\n"
```

When the first child (`reg`) was allocated to register Y, the `%0` would emit "Y", causing assembly errors like "Unknown instruction: Y".

**Solution**: Removed the `%0` prefix from all templates where the first child is `reg`. The value is already in AC when the template runs:
```
reg: ADDI2(reg,INDIRI2(addr))  "    STA _tmp\n    LDA %1\n    ADD _tmp\n"
```

### 5. Missing Rules for Global Address Patterns (SOLVED)

**Problem**: Rules existed for frame-relative addresses (`faddr`) but not for global addresses (`addr`). Operations on global variables used the slower `(reg,reg)` fallback.

**Solution**: Added specific rules for `addr` patterns:
```
reg: SUBI2(INDIRI2(addr),INDIRI2(addr))  "    LDA %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n"  4
reg: BXORI2(INDIRI2(addr),INDIRI2(addr))  "    LDA %0\n    STA _tmp\n    LDA %1\n    XOR _tmp\n"  4
// etc. for AND, OR operations
```

### 6. Increased (reg,reg) Rule Costs (SOLVED)

**Problem**: The generic `(reg,reg)` rules were being selected over more specific patterns due to cost ties.

**Solution**: Increased costs of `(reg,reg)` rules from 4 to 8 to prefer specific patterns:
```
reg: SUBI2(reg,reg)  "    STA _tmp\n    POP\n    SUB _tmp\n"  8
reg: BXORI2(reg,reg)  "    STA _tmp\n    POP\n    XOR _tmp\n"  8
```

## Test Results After Fixes

Before fixes: 14/23 tests passing
After VREG spill fix: 17/23 tests passing
After VREG spill + template fixes: 18/23 tests passing
After division/subtraction addr rules: 19/23 tests passing
After VREGP SUB/bitwise handlers: 21/23 tests passing
After CVUI2/CVII2 char conversion rules: **22/23 tests passing**

Remaining failures (1 test):
1. `08_fibonacci` - Recursive function, VREG global memory issue (architectural limitation)

## Files Modified

- `src/neanderx.md` - Main LCC backend grammar file
  - Modified `emit2()` function for VREG source loading
  - Added emit2() handlers for SUB, BXOR, BAND, BOR with VREGP operands
  - Fixed binary operation templates to remove incorrect `%0` prefix
  - Added VREGP rules for SUBI2, BXORI2, BANDI2, BORI2
  - Added addr-based rules for SUB and bitwise operations
  - Added rules for operations with constants (con2)
  - Increased (reg,reg) rule costs to prefer specific patterns
  - Added CVUI2/CVII2 rules for char-to-int promotion in ADD operations

### CVUI2/CVII2 Char Promotion Fix (SOLVED)

**Problem**: The `10_char` test was failing because char addition (`A + B`) generated incorrect code. The `ADDI2(reg,reg)` template with `%0` and `%1` was emitting register names (X, Y) instead of proper code.

**Root Cause**: When chars are promoted to int for arithmetic, LCC generates `ADDI2(CVUI2(INDIRU1(faddr)), CVUI2(INDIRU1(faddr)))`. The CVUI2 rules reduce each operand to `reg`, and then `ADDI2(reg,reg)` matches. But the `%0` and `%1` in the template emit register names instead of instructions.

**Solution**: Added specific rules to handle char promotion patterns directly:
```
reg: ADDI2(CVUI2(INDIRU1(faddr)),CVUI2(INDIRU1(faddr)))  "    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n"  4
reg: ADDI2(CVUI2(INDIRU1(addr)),CVUI2(INDIRU1(addr)))  "    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n"  4
reg: ADDI2(CVII2(INDIRI1(faddr)),CVII2(INDIRI1(faddr)))  "    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n"  4
reg: ADDI2(CVII2(INDIRI1(addr)),CVII2(INDIRI1(addr)))  "    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n"  4
```

These rules match the complete pattern and emit correct code that loads both operands and adds them.

## Future Work

1. **Stack-based VREG spills**: To support recursive functions properly, VREG spill slots should be allocated on the stack per function call, not in global memory. This would fix the fibonacci test.

   **Note**: A simple caller-save approach (pushing VREGs before CALL) was attempted but failed because it interferes with argument passing - the VREGs get pushed on top of the arguments, corrupting the call stack. A proper fix requires either:
   - Allocating VREG shadow slots in the function frame (requires knowing VREG count before code generation)
   - Or restructuring the backend to use stack-relative VREG addressing

2. **Optimize VREG usage**: Consider reducing unnecessary VREG spills by improving register allocation heuristics.
