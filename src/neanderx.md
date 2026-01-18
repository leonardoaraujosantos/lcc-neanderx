%{
/* =============================================================================
 * NEANDER-X Backend for LCC - 16-bit Version
 * =============================================================================
 *
 * This is an LCC backend for the NEANDER-X 16-bit educational processor.
 *
 * NEANDER-X 16-bit Architecture (Full Feature Set):
 * - 16-bit native word size (int = 2 bytes)
 * - 16-bit address space (64KB via SPI SRAM)
 * - Accumulator-based architecture with index registers
 * - Little-endian byte order
 *
 * Registers:
 * - AC (8-bit)  : Accumulator - main computation register
 * - X  (8-bit)  : Index register - array access, expression temp
 * - Y  (8-bit)  : Index register - MUL high byte, expression temp
 * - PC (16-bit) : Program counter (0x0000-0xFFFF)
 * - SP (16-bit) : Stack pointer (reset: 0x00FF, grows downward)
 * - FP (16-bit) : Frame pointer for local variable access
 * - REM (16-bit): Memory Address Register
 * - RDM (16-bit): Memory Data Register
 *
 * Condition Flags: N (Negative), Z (Zero), C (Carry)
 *
 * Key Instructions Used:
 * - LDA/STA addr     : Load/Store AC from/to memory
 * - LDA/STA addr,X   : Indexed addressing with X
 * - LDA/STA addr,Y   : Indexed addressing with Y
 * - LDA/STA addr,FP  : Frame-relative addressing (locals/params)
 * - LDI imm          : Load immediate to AC
 * - LDXI imm         : Load immediate to X
 * - LDYI imm         : Load immediate to Y
 * - TAX/TXA          : Transfer AC <-> X
 * - TAY/TYA          : Transfer AC <-> Y
 * - INX/INY          : Increment X/Y
 * - ADD/SUB addr     : Arithmetic with memory
 * - ADC/SBC addr     : Arithmetic with carry (multi-byte)
 * - AND/OR/XOR addr  : Bitwise operations
 * - NOT/NEG          : Complement/Negate AC
 * - SHL/SHR/ASR      : Shift operations
 * - MUL              : 16x16 -> 32-bit result (Y:AC = AC * X)
 * - DIV              : AC / X -> AC (quotient), Y (remainder)
 * - MOD              : AC % X -> AC (remainder)
 * - CMP addr         : Compare AC with memory (sets flags)
 * - INC/DEC          : Increment/Decrement AC
 * - PUSH/POP         : Stack operations (16-bit values)
 * - PUSH_FP/POP_FP   : Save/restore frame pointer
 * - TSF/TFS          : Transfer SP <-> FP
 * - CALL/RET         : Subroutine call/return (16-bit addresses)
 * - JMP/JZ/JNZ/JN    : Jump instructions
 * - JC/JNC           : Jump on carry/no carry
 * - JLE/JGT/JGE      : Signed comparison jumps
 * - JBE/JA           : Unsigned comparison jumps
 *
 * Type mapping (16-bit architecture):
 * - char:    1 byte (8-bit character)
 * - short:   2 bytes (16-bit native)
 * - int:     2 bytes (16-bit native)
 * - long:    4 bytes (32-bit using ADC/SBC pairs)
 * - pointer: 2 bytes (16-bit address space)
 * - float:   not supported
 *
 * Calling convention:
 * - Arguments pushed right-to-left on stack (2-byte aligned)
 * - Return value in AC (8-bit) or Y:AC (16-bit, Y=high byte)
 * - Caller cleans up arguments
 * - FP-relative addressing for parameters and locals
 *
 * Stack Frame Layout (16-bit):
 *   Higher addresses
 *   +------------------+
 *   | Parameter N      | <- FP + 4 + 2*(N-1)
 *   | ...              |
 *   | Parameter 1      | <- FP + 4
 *   | Return Address   | <- FP + 2 (16-bit)
 *   | Old FP           | <- FP (16-bit)
 *   | Local Variable 1 | <- FP - 2
 *   | Local Variable 2 | <- FP - 4
 *   +------------------+
 *   Lower addresses    <- SP
 *
 * Register usage strategy:
 * - AC: Primary computation, return values (low byte for 16-bit)
 * - X:  Left operand temp, array index, loop counter
 * - Y:  Right operand temp, MUL high byte, DIV remainder, return high byte
 *
 * =============================================================================
 */

#include "c.h"
#include <string.h>

#define NODEPTR_TYPE Node
#define OP_LABEL(p) ((p)->op)
#define LEFT_CHILD(p) ((p)->kids[0])
#define RIGHT_CHILD(p) ((p)->kids[1])
#define STATE_LABEL(p) ((p)->x.state)

/* Register indices - AC is primary, X and Y are temporaries */
enum { REG_AC=0, REG_X=1, REG_Y=2, REG_MAX=3 };

#define IREG 1    /* Integer register class */

static Symbol intreg[32];  /* Integer register array */
static Symbol intregw;     /* Wildcard for integer registers */
static Symbol xreg;        /* X register symbol */
static Symbol yreg;        /* Y register symbol */

static int cseg;           /* Current segment */
static int tmpcount;       /* Temporary variable counter */
static int labelcnt;       /* Label counter for generated labels */

/* VREG-to-slot mapping for spill/reload */
#define MAX_VREG_SLOTS 32
static Symbol vreg_symbols[MAX_VREG_SLOTS];
static int next_vreg_slot;

static char rcsid[] = "$Id: neanderx.md v2.0 - Enhanced for full NEANDER-X $";

/* Forward declarations */
static void address(Symbol, Symbol, long);
static void defaddress(Symbol);
static void defconst(int, int, Value);
static void defstring(int, char *);
static void defsymbol(Symbol);
static void doarg(Node);
static void emit2(Node);
static void export(Symbol);
static void clobber(Node);
static void function(Symbol, Symbol [], Symbol [], int);
static void global(Symbol);
static void import(Symbol);
static void local(Symbol);
static void progbeg(int, char **);
static void progend(void);
static void segment(int);
static void space(int);
static void target(Node);
static Symbol rmap(int);
static void blkfetch(int, int, int, int);
static void blkstore(int, int, int, int);
static void blkloop(int, int, int, int, int, int[]);

/* Helper macros for constant ranges */
#define range(p, lo, hi) ((p)->syms[0]->u.c.v.i >= (lo) && (p)->syms[0]->u.c.v.i <= (hi) ? 0 : LBURG_MAX)

/* Helpers for 16-bit operations */
static int needs16bit(Node p) {
    return opsize(p->op) == 2;
}

/* Get or allocate a memory slot for a VREG symbol */
static int get_vreg_slot(Symbol reg) {
    int i;
    /* Look for existing mapping */
    for (i = 0; i < next_vreg_slot; i++) {
        if (vreg_symbols[i] == reg) {
            return i;
        }
    }
    /* Allocate new slot */
    if (next_vreg_slot < MAX_VREG_SLOTS) {
        vreg_symbols[next_vreg_slot] = reg;
        return next_vreg_slot++;
    }
    /* Fallback - shouldn't happen */
    return 0;
}

%}

%start stmt

%term CNSTI1=1045
%term CNSTU1=1046
%term CNSTP2=2071
%term CNSTI2=2069
%term CNSTU2=2070
%term CNSTI4=4117
%term CNSTU4=4118
%term CNSTP4=4119

%term ARGB=41
%term ARGI1=1061
%term ARGU1=1062
%term ARGI2=2085
%term ARGU2=2086
%term ARGP2=2087
%term ARGI4=4133
%term ARGU4=4134
%term ARGP4=4135

%term ASGNB=57
%term ASGNI1=1077
%term ASGNU1=1078
%term ASGNI2=2101
%term ASGNU2=2102
%term ASGNP2=2103
%term ASGNI4=4149
%term ASGNU4=4150
%term ASGNP4=4151

%term INDIRB=73
%term INDIRI1=1093
%term INDIRU1=1094
%term INDIRI2=2117
%term INDIRU2=2118
%term INDIRP2=2119
%term INDIRI4=4165
%term INDIRU4=4166
%term INDIRP4=4167

%term CVII1=1157
%term CVII2=2181
%term CVII4=4229
%term CVIU1=1158
%term CVIU2=2182
%term CVIU4=4230
%term CVUI1=1205
%term CVUI2=2229
%term CVUI4=4277
%term CVUU1=1206
%term CVUU2=2230
%term CVUU4=4278
%term CVPU2=2198
%term CVUP2=2231
%term CVPU4=4246
%term CVUP4=4279

%term NEGI1=1221
%term NEGI2=2245

%term CALLB=217
%term CALLI1=1237
%term CALLU1=1238
%term CALLI2=2261
%term CALLU2=2262
%term CALLP2=2263
%term CALLV=216
%term CALLI4=4309
%term CALLU4=4310
%term CALLP4=4311

%term RETI1=1269
%term RETU1=1270
%term RETI2=2293
%term RETU2=2294
%term RETP2=2295
%term RETV=248
%term RETI4=4341
%term RETU4=4342
%term RETP4=4343

%term ADDRGP2=2311
%term ADDRFP2=2327
%term ADDRLP2=2343
%term ADDRGP4=4359
%term ADDRFP4=4375
%term ADDRLP4=4391

%term ADDI1=1333
%term ADDU1=1334
%term ADDI2=2357
%term ADDU2=2358
%term ADDP2=2359
%term ADDI4=4405
%term ADDU4=4406

%term SUBI1=1349
%term SUBU1=1350
%term SUBI2=2373
%term SUBU2=2374
%term SUBI4=4421
%term SUBU4=4422

%term LSHI1=1365
%term LSHU1=1366
%term LSHI2=2389
%term LSHU2=2390

%term RSHI1=1397
%term RSHU1=1398
%term RSHI2=2421
%term RSHU2=2422

%term MODI1=1381
%term MODU1=1382
%term MODI2=2405
%term MODU2=2406

%term BANDI1=1413
%term BANDU1=1414
%term BANDI2=2437
%term BANDU2=2438

%term BCOMI1=1429
%term BCOMU1=1430
%term BCOMI2=2453
%term BCOMU2=2454

%term BORI1=1445
%term BORU1=1446
%term BORI2=2469
%term BORU2=2470

%term BXORI1=1461
%term BXORU1=1462
%term BXORI2=2485
%term BXORU2=2486

%term DIVI1=1477
%term DIVU1=1478
%term DIVI2=2501
%term DIVU2=2502

%term MULI1=1493
%term MULU1=1494
%term MULI2=2517
%term MULU2=2518

%term EQI1=1509
%term EQU1=1510
%term EQI2=2533
%term EQU2=2534

%term GEI1=1525
%term GEU1=1526
%term GEI2=2549
%term GEU2=2550

%term GTI1=1541
%term GTU1=1542
%term GTI2=2565
%term GTU2=2566

%term LEI1=1557
%term LEU1=1558
%term LEI2=2581
%term LEU2=2582

%term LTI1=1573
%term LTU1=1574
%term LTI2=2597
%term LTU2=2598

%term NEI1=1589
%term NEU1=1590
%term NEI2=2613
%term NEU2=2614

%term JUMPV=584
%term LABELV=600

%term LOADI1=1253
%term LOADU1=1254
%term LOADI2=2277
%term LOADU2=2278
%term LOADP2=2279
%term LOADI4=4325
%term LOADU4=4326
%term LOADP4=4327

%term VREGP=711

%%

reg: INDIRI1(VREGP)    "# read vreg\n"
reg: INDIRU1(VREGP)    "# read vreg\n"
reg: INDIRI2(VREGP)    "# read vreg\n"
reg: INDIRU2(VREGP)    "# read vreg\n"
reg: INDIRP2(VREGP)    "# read vreg\n"
reg: INDIRI4(VREGP)    "# read vreg\n"
reg: INDIRU4(VREGP)    "# read vreg\n"
reg: INDIRP4(VREGP)    "# read vreg\n"

reg: ADDI2(INDIRI2(VREGP),INDIRI2(VREGP))  "# add vreg+vreg\n"  3
reg: ADDU2(INDIRU2(VREGP),INDIRU2(VREGP))  "# add vreg+vreg\n"  3
reg: ADDP2(INDIRP2(VREGP),INDIRI2(VREGP))  "# add vreg+vreg\n"  3

reg: ADDI2(INDIRI2(VREGP),con2)  "# add vreg+const\n"  2
reg: ADDU2(INDIRU2(VREGP),con2)  "# add vreg+const\n"  2

reg: MULI2(INDIRI2(VREGP),INDIRI2(VREGP))  "# mul vreg*vreg\n"  3
reg: MULU2(INDIRU2(VREGP),INDIRU2(VREGP))  "# mul vreg*vreg\n"  3

reg: SUBI2(INDIRI2(VREGP),INDIRI2(VREGP))  "# sub vreg-vreg\n"  3
reg: SUBU2(INDIRU2(VREGP),INDIRU2(VREGP))  "# sub vreg-vreg\n"  3

reg: BXORI2(INDIRI2(VREGP),INDIRI2(VREGP))  "# xor vreg^vreg\n"  3
reg: BXORU2(INDIRU2(VREGP),INDIRU2(VREGP))  "# xor vreg^vreg\n"  3

reg: BANDI2(INDIRI2(VREGP),INDIRI2(VREGP))  "# and vreg&vreg\n"  3
reg: BANDU2(INDIRU2(VREGP),INDIRU2(VREGP))  "# and vreg&vreg\n"  3

reg: BORI2(INDIRI2(VREGP),INDIRI2(VREGP))  "# or vreg|vreg\n"  3
reg: BORU2(INDIRU2(VREGP),INDIRU2(VREGP))  "# or vreg|vreg\n"  3

stmt: ASGNI1(VREGP,reg)  "# write vreg\n"
stmt: ASGNU1(VREGP,reg)  "# write vreg\n"
stmt: ASGNI2(VREGP,reg)  "# write vreg\n"
stmt: ASGNU2(VREGP,reg)  "# write vreg\n"
stmt: ASGNP2(VREGP,reg)  "# write vreg\n"
stmt: ASGNI4(VREGP,reg)  "# write vreg\n"
stmt: ASGNU4(VREGP,reg)  "# write vreg\n"
stmt: ASGNP4(VREGP,reg)  "# write vreg\n"


con1: CNSTI1  "%a"
con1: CNSTU1  "%a"

con2: CNSTI2  "%a"
con2: CNSTU2  "%a"
con2: CNSTP2  "%a"

con4: CNSTI4  "%a"
con4: CNSTU4  "%a"
con4: CNSTP4  "%a"

conN: CNSTI1  "%a"  range(a, 1, 1)
conN: CNSTU1  "%a"  range(a, 1, 1)

reg: con1  "    LDI %0\n"  1

reg: con2  "    LDI %0\n"  1

reg: con4  "    LDI lo(%0)\n    PUSH\n    LDI hi(%0)\n"  3

addr: ADDRGP2  "%a"
addr: ADDRGP4  "%a"

faddr: ADDRFP2  "%a,FP"
faddr: ADDRLP2  "%a,FP"
faddr: ADDRFP4  "%a,FP"
faddr: ADDRLP4  "%a,FP"

addr: faddr  "%0"

reg: ADDRGP2  "    LDI %a\n"  1
reg: ADDRFP2  "    LDI %a\n"  1
reg: ADDRLP2  "    LDI %a\n"  1

reg: INDIRI1(faddr)  "    LDA %0\n"  1
reg: INDIRU1(faddr)  "    LDA %0\n"  1
reg: INDIRI2(faddr)  "    LDA %0\n"  1
reg: INDIRU2(faddr)  "    LDA %0\n"  1
reg: INDIRP2(faddr)  "    LDA %0\n"  1

stmt: ASGNI1(faddr,reg)  "    STA %0\n"  1
stmt: ASGNU1(faddr,reg)  "    STA %0\n"  1
stmt: ASGNI2(faddr,reg)  "    STA %0\n"  1
stmt: ASGNU2(faddr,reg)  "    STA %0\n"  1
stmt: ASGNP2(faddr,reg)  "    STA %0\n"  1

reg: INDIRI1(addr)  "    LDA %0\n"  2
reg: INDIRU1(addr)  "    LDA %0\n"  2

reg: INDIRI2(addr)  "    LDA %0\n"  2
reg: INDIRU2(addr)  "    LDA %0\n"  2
reg: INDIRP2(addr)  "    LDA %0\n"  2

reg: INDIRI4(addr)  "    LDA %0\n    PUSH\n    LDA %0+2\n"  4
reg: INDIRU4(addr)  "    LDA %0\n    PUSH\n    LDA %0+2\n"  4
reg: INDIRP4(addr)  "    LDA %0\n    PUSH\n    LDA %0+2\n"  4

stmt: ASGNI1(addr,reg)  "    STA %0\n"  2
stmt: ASGNU1(addr,reg)  "    STA %0\n"  2

stmt: ASGNI2(addr,reg)  "    STA %0\n"  2
stmt: ASGNU2(addr,reg)  "    STA %0\n"  2
stmt: ASGNP2(addr,reg)  "    STA %0\n"  2

stmt: ASGNI4(addr,reg)  "    STA %0+2\n    POP\n    STA %0\n"  4
stmt: ASGNU4(addr,reg)  "    STA %0+2\n    POP\n    STA %0\n"  4
stmt: ASGNP4(addr,reg)  "    STA %0+2\n    POP\n    STA %0\n"  4

reg: INDIRI1(ADDI2(addr,reg))  "    TAX\n    LDA %0,X\n"  3
reg: INDIRU1(ADDI2(addr,reg))  "    TAX\n    LDA %0,X\n"  3
reg: INDIRI1(ADDP2(addr,reg))  "    TAX\n    LDA %0,X\n"  3
reg: INDIRU1(ADDP2(addr,reg))  "    TAX\n    LDA %0,X\n"  3
reg: INDIRI1(ADDP2(reg,addr))  "    TAX\n    LDA %1,X\n"  3
reg: INDIRU1(ADDP2(reg,addr))  "    TAX\n    LDA %1,X\n"  3

stmt: ASGNI1(ADDI2(addr,reg),reg)  "    TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n"  5
stmt: ASGNU1(ADDI2(addr,reg),reg)  "    TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n"  5
stmt: ASGNI1(ADDP2(addr,reg),reg)  "    TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n"  5
stmt: ASGNU1(ADDP2(addr,reg),reg)  "    TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n"  5
stmt: ASGNI1(ADDP2(reg,addr),reg)  "    TAY\n    POP\n    TAX\n    TYA\n    STA %1,X\n"  5
stmt: ASGNU1(ADDP2(reg,addr),reg)  "    TAY\n    POP\n    TAX\n    TYA\n    STA %1,X\n"  5

reg: ADDI1(INDIRI1(addr),INDIRI1(addr))  "    LDA %0\n    ADD %1\n"  2
reg: ADDU1(INDIRU1(addr),INDIRU1(addr))  "    LDA %0\n    ADD %1\n"  2
reg: ADDI1(INDIRU1(addr),INDIRU1(addr))  "    LDA %0\n    ADD %1\n"  2
reg: ADDI1(LOADI1(INDIRU1(addr)),LOADI1(INDIRU1(addr)))  "    LDA %0\n    ADD %1\n"  2
reg: ADDU1(LOADU1(INDIRU1(addr)),LOADU1(INDIRU1(addr)))  "    LDA %0\n    ADD %1\n"  2

reg: ADDI1(reg,reg)  "    ADDX\n"  10
reg: ADDU1(reg,reg)  "    ADDX\n"  10

reg: ADDI1(reg,INDIRI1(addr))  "    ADD %1\n"  1
reg: ADDU1(reg,INDIRU1(addr))  "    ADD %1\n"  1
reg: ADDI1(reg,INDIRU1(addr))  "    ADD %1\n"  1

reg: ADDI1(reg,conN)  "    INC\n"  1
reg: ADDU1(reg,conN)  "    INC\n"  1

reg: SUBI1(INDIRI1(addr),INDIRI1(addr))  "    LDA %0\n    SUB %1\n"  2
reg: SUBU1(INDIRU1(addr),INDIRU1(addr))  "    LDA %0\n    SUB %1\n"  2
reg: SUBI1(INDIRU1(addr),INDIRU1(addr))  "    LDA %0\n    SUB %1\n"  2
reg: SUBI1(LOADI1(INDIRU1(addr)),LOADI1(INDIRU1(addr)))  "    LDA %0\n    SUB %1\n"  2
reg: SUBU1(LOADU1(INDIRU1(addr)),LOADU1(INDIRU1(addr)))  "    LDA %0\n    SUB %1\n"  2

reg: SUBI1(reg,reg)  "    SUBX\n"  10
reg: SUBU1(reg,reg)  "    SUBX\n"  10

reg: SUBI1(reg,INDIRI1(addr))  "    SUB %1\n"  1
reg: SUBU1(reg,INDIRU1(addr))  "    SUB %1\n"  1
reg: SUBI1(reg,INDIRU1(addr))  "    SUB %1\n"  1

reg: SUBI1(reg,conN)  "    DEC\n"  1
reg: SUBU1(reg,conN)  "    DEC\n"  1

reg: NEGI1(reg)  "    NEG\n"  1

reg: ADDI2(INDIRI2(faddr),con2)  "    LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n"  3
reg: ADDU2(INDIRU2(faddr),con2)  "    LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n"  3
reg: ADDP2(INDIRP2(faddr),con2)  "    LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n"  3

reg: ADDI2(INDIRI2(faddr),INDIRI2(faddr))  "    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n"  4
reg: ADDU2(INDIRU2(faddr),INDIRU2(faddr))  "    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n"  4
reg: ADDP2(INDIRP2(faddr),INDIRI2(faddr))  "    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n"  4

reg: ADDI2(INDIRI2(addr),con2)  "    LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n"  3
reg: ADDU2(INDIRU2(addr),con2)  "    LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n"  3

reg: ADDI2(INDIRI2(addr),INDIRI2(addr))  "    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n"  4
reg: ADDU2(INDIRU2(addr),INDIRU2(addr))  "    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n"  4

reg: ADDI2(reg,INDIRI2(addr))  "    STA _tmp\n    LDA %1\n    ADD _tmp\n"  3
reg: ADDU2(reg,INDIRU2(addr))  "    STA _tmp\n    LDA %1\n    ADD _tmp\n"  3

reg: ADDI2(reg,INDIRI2(faddr))  "    STA _tmp\n    LDA %1\n    ADD _tmp\n"  3
reg: ADDU2(reg,INDIRU2(faddr))  "    STA _tmp\n    LDA %1\n    ADD _tmp\n"  3
reg: ADDP2(reg,INDIRP2(faddr))  "    STA _tmp\n    LDA %1\n    ADD _tmp\n"  3

reg: ADDI2(reg,con2)  "    STA _tmp\n    LDI %1\n    ADD _tmp\n"  3
reg: ADDU2(reg,con2)  "    STA _tmp\n    LDI %1\n    ADD _tmp\n"  3

reg: ADDI2(CVUI2(INDIRI2(faddr)),CVUI2(INDIRI2(faddr)))  "    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n"  4
reg: ADDU2(CVUI2(INDIRU2(faddr)),CVUI2(INDIRU2(faddr)))  "    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n"  4
reg: ADDI2(CVUI2(INDIRI2(addr)),CVUI2(INDIRI2(addr)))  "    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n"  4
reg: ADDU2(CVUI2(INDIRU2(addr)),CVUI2(INDIRU2(addr)))  "    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n"  4

reg: ADDI2(CVUI2(INDIRU1(faddr)),CVUI2(INDIRU1(faddr)))  "    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n"  4
reg: ADDI2(CVUI2(INDIRU1(addr)),CVUI2(INDIRU1(addr)))  "    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n"  4
reg: ADDI2(CVII2(INDIRI1(faddr)),CVII2(INDIRI1(faddr)))  "    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n"  4
reg: ADDI2(CVII2(INDIRI1(addr)),CVII2(INDIRI1(addr)))  "    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n"  4

reg: ADDI2(reg,reg)  "%0    STA _tmp\n%1    ADD _tmp\n"  8
reg: ADDU2(reg,reg)  "%0    STA _tmp\n%1    ADD _tmp\n"  8
reg: ADDP2(reg,reg)  "%0    STA _tmp\n%1    ADD _tmp\n"  8
addr: ADDP2(addr,reg)  "%0"  1

reg: SUBI2(INDIRI2(faddr),con2)  "    LDI %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n"  3
reg: SUBU2(INDIRU2(faddr),con2)  "    LDI %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n"  3

reg: SUBI2(INDIRI2(faddr),INDIRI2(faddr))  "    LDA %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n"  4
reg: SUBU2(INDIRU2(faddr),INDIRU2(faddr))  "    LDA %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n"  4

reg: SUBI2(INDIRI2(addr),con2)  "    LDI %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n"  3
reg: SUBU2(INDIRU2(addr),con2)  "    LDI %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n"  3

reg: SUBI2(INDIRI2(addr),INDIRI2(addr))  "    LDA %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n"  4
reg: SUBU2(INDIRU2(addr),INDIRU2(addr))  "    LDA %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n"  4

reg: SUBI2(reg,INDIRI2(addr))  "    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n"  5
reg: SUBU2(reg,INDIRU2(addr))  "    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n"  5

reg: SUBI2(reg,INDIRI2(faddr))  "    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n"  5
reg: SUBU2(reg,INDIRU2(faddr))  "    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n"  5

reg: SUBI2(reg,con2)  "    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n"  4
reg: SUBU2(reg,con2)  "    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n"  4

reg: SUBI2(reg,reg)  "    STA _tmp\n    POP\n    SUB _tmp\n"  8
reg: SUBU2(reg,reg)  "    STA _tmp\n    POP\n    SUB _tmp\n"  8

reg: NEGI2(reg)  "    NEG\n"  1

reg: ADDI4(reg,reg)  "    STA _tmp\n    POP\n    STA _tmp_hi\n    POP\n    STA _tmp2_hi\n    POP\n    ADD _tmp\n    PUSH\n    LDA _tmp2_hi\n    ADC _tmp_hi\n"  10
reg: ADDU4(reg,reg)  "    STA _tmp\n    POP\n    STA _tmp_hi\n    POP\n    STA _tmp2_hi\n    POP\n    ADD _tmp\n    PUSH\n    LDA _tmp2_hi\n    ADC _tmp_hi\n"  10

reg: SUBI4(reg,reg)  "    STA _tmp\n    POP\n    STA _tmp_hi\n    POP\n    STA _tmp2_hi\n    POP\n    SUB _tmp\n    PUSH\n    LDA _tmp2_hi\n    SBC _tmp_hi\n"  10
reg: SUBU4(reg,reg)  "    STA _tmp\n    POP\n    STA _tmp_hi\n    POP\n    STA _tmp2_hi\n    POP\n    SUB _tmp\n    PUSH\n    LDA _tmp2_hi\n    SBC _tmp_hi\n"  10

reg: MULI1(reg,reg)  "    TAX\n    POP\n    MUL\n"  3
reg: MULU1(reg,reg)  "    TAX\n    POP\n    MUL\n"  3

reg: MULI2(reg,reg)  "    TAX\n    POP\n    MUL\n"  3
reg: MULU2(reg,reg)  "    TAX\n    POP\n    MUL\n"  3

reg: DIVI1(reg,reg)  "    TAX\n    POP\n    DIV\n"  3
reg: DIVU1(reg,reg)  "    TAX\n    POP\n    DIV\n"  3

reg: DIVI2(reg,reg)  "    TAX\n    POP\n    DIV\n"  3
reg: DIVU2(reg,reg)  "    TAX\n    POP\n    DIV\n"  3

reg: DIVI2(INDIRI2(faddr),INDIRI2(faddr))  "    LDA %1\n    TAX\n    LDA %0\n    DIV\n"  4
reg: DIVU2(INDIRU2(faddr),INDIRU2(faddr))  "    LDA %1\n    TAX\n    LDA %0\n    DIV\n"  4

reg: DIVI2(reg,INDIRI2(faddr))  "    STA _tmp\n    LDA %1\n    TAX\n    LDA _tmp\n    DIV\n"  5
reg: DIVU2(reg,INDIRU2(faddr))  "    STA _tmp\n    LDA %1\n    TAX\n    LDA _tmp\n    DIV\n"  5

reg: MODI1(reg,reg)  "    TAX\n    POP\n    MOD\n"  3
reg: MODU1(reg,reg)  "    TAX\n    POP\n    MOD\n"  3

reg: MODI2(reg,reg)  "    TAX\n    POP\n    MOD\n"  3
reg: MODU2(reg,reg)  "    TAX\n    POP\n    MOD\n"  3

reg: MODI2(INDIRI2(faddr),INDIRI2(faddr))  "    LDA %1\n    TAX\n    LDA %0\n    MOD\n"  4
reg: MODU2(INDIRU2(faddr),INDIRU2(faddr))  "    LDA %1\n    TAX\n    LDA %0\n    MOD\n"  4

reg: MODI2(reg,INDIRI2(faddr))  "    STA _tmp\n    LDA %1\n    TAX\n    LDA _tmp\n    MOD\n"  5
reg: MODU2(reg,INDIRU2(faddr))  "    STA _tmp\n    LDA %1\n    TAX\n    LDA _tmp\n    MOD\n"  5

reg: BANDI1(INDIRI1(addr),INDIRI1(addr))  "    LDA %0\n    AND %1\n"  2
reg: BANDU1(INDIRU1(addr),INDIRU1(addr))  "    LDA %0\n    AND %1\n"  2

reg: BANDI1(reg,reg)  "    ANDX\n"  10
reg: BANDU1(reg,reg)  "    ANDX\n"  10

reg: BANDI1(reg,INDIRI1(addr))  "    AND %1\n"  1
reg: BANDU1(reg,INDIRU1(addr))  "    AND %1\n"  1

reg: BORI1(INDIRI1(addr),INDIRI1(addr))  "    LDA %0\n    OR %1\n"  2
reg: BORU1(INDIRU1(addr),INDIRU1(addr))  "    LDA %0\n    OR %1\n"  2

reg: BORI1(reg,reg)  "    ORX\n"  10
reg: BORU1(reg,reg)  "    ORX\n"  10

reg: BORI1(reg,INDIRI1(addr))  "    OR %1\n"  1
reg: BORU1(reg,INDIRU1(addr))  "    OR %1\n"  1

reg: BXORI1(INDIRI1(addr),INDIRI1(addr))  "    LDA %0\n    XOR %1\n"  2
reg: BXORU1(INDIRU1(addr),INDIRU1(addr))  "    LDA %0\n    XOR %1\n"  2

reg: BXORI1(reg,reg)  "    XORX\n"  10
reg: BXORU1(reg,reg)  "    XORX\n"  10

reg: BXORI1(reg,INDIRI1(addr))  "    XOR %1\n"  1
reg: BXORU1(reg,INDIRU1(addr))  "    XOR %1\n"  1

reg: BCOMI1(reg)  "    NOT\n"  1
reg: BCOMU1(reg)  "    NOT\n"  1

reg: BANDI2(reg,reg)  "    STA _tmp\n    POP\n    AND _tmp\n"  8
reg: BANDU2(reg,reg)  "    STA _tmp\n    POP\n    AND _tmp\n"  8

reg: BANDI2(INDIRI2(faddr),INDIRI2(faddr))  "    LDA %0\n    STA _tmp\n    LDA %1\n    AND _tmp\n"  2
reg: BANDU2(INDIRU2(faddr),INDIRU2(faddr))  "    LDA %0\n    STA _tmp\n    LDA %1\n    AND _tmp\n"  2

reg: BANDI2(reg,INDIRI2(faddr))  "    STA _tmp\n    LDA %1\n    AND _tmp\n"  3
reg: BANDU2(reg,INDIRU2(faddr))  "    STA _tmp\n    LDA %1\n    AND _tmp\n"  3

reg: BANDI2(INDIRI2(addr),INDIRI2(addr))  "    LDA %0\n    STA _tmp\n    LDA %1\n    AND _tmp\n"  4
reg: BANDU2(INDIRU2(addr),INDIRU2(addr))  "    LDA %0\n    STA _tmp\n    LDA %1\n    AND _tmp\n"  4

reg: BANDI2(reg,con2)  "    STA _tmp\n    LDI %1\n    AND _tmp\n"  3
reg: BANDU2(reg,con2)  "    STA _tmp\n    LDI %1\n    AND _tmp\n"  3

reg: BANDI2(INDIRI2(faddr),con2)  "    LDA %0\n    STA _tmp\n    LDI %1\n    AND _tmp\n"  4
reg: BANDU2(INDIRU2(faddr),con2)  "    LDA %0\n    STA _tmp\n    LDI %1\n    AND _tmp\n"  4

reg: BANDI2(reg,INDIRI2(addr))  "    STA _tmp\n    LDA %1\n    AND _tmp\n"  3
reg: BANDU2(reg,INDIRU2(addr))  "    STA _tmp\n    LDA %1\n    AND _tmp\n"  3

reg: BORI2(reg,reg)  "    STA _tmp\n    POP\n    OR _tmp\n"  8
reg: BORU2(reg,reg)  "    STA _tmp\n    POP\n    OR _tmp\n"  8

reg: BORI2(INDIRI2(faddr),INDIRI2(faddr))  "    LDA %0\n    STA _tmp\n    LDA %1\n    OR _tmp\n"  2
reg: BORU2(INDIRU2(faddr),INDIRU2(faddr))  "    LDA %0\n    STA _tmp\n    LDA %1\n    OR _tmp\n"  2

reg: BORI2(reg,INDIRI2(faddr))  "    STA _tmp\n    LDA %1\n    OR _tmp\n"  3
reg: BORU2(reg,INDIRU2(faddr))  "    STA _tmp\n    LDA %1\n    OR _tmp\n"  3

reg: BORI2(INDIRI2(addr),INDIRI2(addr))  "    LDA %0\n    STA _tmp\n    LDA %1\n    OR _tmp\n"  4
reg: BORU2(INDIRU2(addr),INDIRU2(addr))  "    LDA %0\n    STA _tmp\n    LDA %1\n    OR _tmp\n"  4

reg: BORI2(reg,con2)  "    STA _tmp\n    LDI %1\n    OR _tmp\n"  3
reg: BORU2(reg,con2)  "    STA _tmp\n    LDI %1\n    OR _tmp\n"  3

reg: BORI2(INDIRI2(faddr),con2)  "    LDA %0\n    STA _tmp\n    LDI %1\n    OR _tmp\n"  4
reg: BORU2(INDIRU2(faddr),con2)  "    LDA %0\n    STA _tmp\n    LDI %1\n    OR _tmp\n"  4

reg: BORI2(reg,INDIRI2(addr))  "    STA _tmp\n    LDA %1\n    OR _tmp\n"  3
reg: BORU2(reg,INDIRU2(addr))  "    STA _tmp\n    LDA %1\n    OR _tmp\n"  3

reg: BXORI2(reg,reg)  "    STA _tmp\n    POP\n    XOR _tmp\n"  8
reg: BXORU2(reg,reg)  "    STA _tmp\n    POP\n    XOR _tmp\n"  8

reg: BXORI2(INDIRI2(faddr),INDIRI2(faddr))  "    LDA %0\n    STA _tmp\n    LDA %1\n    XOR _tmp\n"  2
reg: BXORU2(INDIRU2(faddr),INDIRU2(faddr))  "    LDA %0\n    STA _tmp\n    LDA %1\n    XOR _tmp\n"  2

reg: BXORI2(reg,INDIRI2(faddr))  "    STA _tmp\n    LDA %1\n    XOR _tmp\n"  3
reg: BXORU2(reg,INDIRU2(faddr))  "    STA _tmp\n    LDA %1\n    XOR _tmp\n"  3

reg: BXORI2(INDIRI2(addr),INDIRI2(addr))  "    LDA %0\n    STA _tmp\n    LDA %1\n    XOR _tmp\n"  4
reg: BXORU2(INDIRU2(addr),INDIRU2(addr))  "    LDA %0\n    STA _tmp\n    LDA %1\n    XOR _tmp\n"  4

reg: BXORI2(reg,con2)  "    STA _tmp\n    LDI %1\n    XOR _tmp\n"  3
reg: BXORU2(reg,con2)  "    STA _tmp\n    LDI %1\n    XOR _tmp\n"  3

reg: BXORI2(INDIRI2(faddr),con2)  "    LDA %0\n    STA _tmp\n    LDI %1\n    XOR _tmp\n"  4
reg: BXORU2(INDIRU2(faddr),con2)  "    LDA %0\n    STA _tmp\n    LDI %1\n    XOR _tmp\n"  4

reg: BXORI2(reg,INDIRI2(addr))  "    STA _tmp\n    LDA %1\n    XOR _tmp\n"  3
reg: BXORU2(reg,INDIRU2(addr))  "    STA _tmp\n    LDA %1\n    XOR _tmp\n"  3

reg: BCOMI2(reg)  "    NOT\n"  1
reg: BCOMU2(reg)  "    NOT\n"  1

reg: LSHI2(reg,conN)  "    SHL\n"  1
reg: LSHU2(reg,conN)  "    SHL\n"  1
reg: RSHU2(reg,conN)  "    SHR\n"  1
reg: RSHI2(reg,conN)  "    ASR\n"  1

reg: LSHI2(reg,reg)  "    TAX\n    POP\n    TAY\n_shl2_%a:\n    TXA\n    JZ _shl2d_%a\n    TYA\n    SHL\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shl2_%a\n_shl2d_%a:\n    TYA\n"  15
reg: LSHU2(reg,reg)  "    TAX\n    POP\n    TAY\n_shl2_%a:\n    TXA\n    JZ _shl2d_%a\n    TYA\n    SHL\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shl2_%a\n_shl2d_%a:\n    TYA\n"  15
reg: RSHU2(reg,reg)  "    TAX\n    POP\n    TAY\n_shr2_%a:\n    TXA\n    JZ _shr2d_%a\n    TYA\n    SHR\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shr2_%a\n_shr2d_%a:\n    TYA\n"  15
reg: RSHI2(reg,reg)  "    TAX\n    POP\n    TAY\n_asr2_%a:\n    TXA\n    JZ _asr2d_%a\n    TYA\n    ASR\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _asr2_%a\n_asr2d_%a:\n    TYA\n"  15

reg: LSHI1(reg,conN)  "    SHL\n"  1
reg: LSHU1(reg,conN)  "    SHL\n"  1

reg: RSHU1(reg,conN)  "    SHR\n"  1
reg: RSHI1(reg,conN)  "    ASR\n"  1

reg: LSHI1(reg,reg)  "    TAX\n    POP\n    TAY\n_shl_%a:\n    TXA\n    JZ _shld_%a\n    TYA\n    SHL\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shl_%a\n_shld_%a:\n    TYA\n"  15
reg: LSHU1(reg,reg)  "    TAX\n    POP\n    TAY\n_shl_%a:\n    TXA\n    JZ _shld_%a\n    TYA\n    SHL\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shl_%a\n_shld_%a:\n    TYA\n"  15

reg: RSHU1(reg,reg)  "    TAX\n    POP\n    TAY\n_shr_%a:\n    TXA\n    JZ _shrd_%a\n    TYA\n    SHR\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shr_%a\n_shrd_%a:\n    TYA\n"  15
reg: RSHI1(reg,reg)  "    TAX\n    POP\n    TAY\n_asr_%a:\n    TXA\n    JZ _asrd_%a\n    TYA\n    ASR\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _asr_%a\n_asrd_%a:\n    TYA\n"  15

reg: CVII1(reg)  "    AND _mask_ff\n"  1
reg: CVIU1(reg)  "    AND _mask_ff\n"  1
reg: CVUI1(reg)  "    AND _mask_ff\n"  1
reg: CVUU1(reg)  "    AND _mask_ff\n"  1

reg: CVII2(reg)  "; cvii2 - sign extend 8 to 16\n"  0
reg: CVIU2(reg)  "; cviu2 - zero extend 8 to 16\n"  0
reg: CVUI2(reg)  "; cvui2 - already 16-bit\n"  0
reg: CVUU2(reg)  "; cvuu2 - already 16-bit\n"  0

reg: CVII1(INDIRI2(addr))  "    LDA %0\n    AND _mask_ff\n"  2
reg: CVUU1(INDIRU2(addr))  "    LDA %0\n    AND _mask_ff\n"  2

reg: CVPU2(reg)  "; cvpu2\n"  0
reg: CVUP2(reg)  "; cvup2\n"  0

reg: CVII4(reg)  "    TAY\n    JN _sx4_%a\n    LDI 0\n    JMP _sx4d_%a\n_sx4_%a:\n    LDI 0xFFFF\n_sx4d_%a:\n    PUSH\n    TYA\n"  8
reg: CVIU4(reg)  "    PUSH\n    LDI 0\n"  2
reg: CVUI4(reg)  "    PUSH\n    LDI 0\n"  2
reg: CVUU4(reg)  "    PUSH\n    LDI 0\n"  2
reg: CVPU4(reg)  "    PUSH\n    LDI 0\n"  2
reg: CVUP4(reg)  "; cvup4 - truncate to pointer\n"  0

stmt: LABELV  "%a:\n"

stmt: JUMPV(addr)  "    JMP %0\n"  1
stmt: JUMPV(reg)   "    JMP %0\n"  10

stmt: EQI1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JZ %a\n"  5
stmt: EQU1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JZ %a\n"  5

stmt: EQI1(reg,INDIRI1(addr))  "    CMP %1\n    JZ %a\n"  3
stmt: EQU1(reg,INDIRU1(addr))  "    CMP %1\n    JZ %a\n"  3

stmt: NEI1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JNZ %a\n"  5
stmt: NEU1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JNZ %a\n"  5

stmt: NEI1(reg,INDIRI1(addr))  "    CMP %1\n    JNZ %a\n"  3
stmt: NEU1(reg,INDIRU1(addr))  "    CMP %1\n    JNZ %a\n"  3

stmt: LTI1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JN %a\n"  5
stmt: LTI1(reg,INDIRI1(addr))  "    CMP %1\n    JN %a\n"  3

stmt: LTU1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JC %a\n"  5
stmt: LTU1(reg,INDIRU1(addr))  "    CMP %1\n    JC %a\n"  3

stmt: LEI1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JLE %a\n"  5
stmt: LEI1(reg,INDIRI1(addr))  "    CMP %1\n    JLE %a\n"  3

stmt: LEU1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JBE %a\n"  5
stmt: LEU1(reg,INDIRU1(addr))  "    CMP %1\n    JBE %a\n"  3

stmt: GTI1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JGT %a\n"  5
stmt: GTI1(reg,INDIRI1(addr))  "    CMP %1\n    JGT %a\n"  3

stmt: GTU1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JA %a\n"  5
stmt: GTU1(reg,INDIRU1(addr))  "    CMP %1\n    JA %a\n"  3

stmt: GEI1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JGE %a\n"  5
stmt: GEI1(reg,INDIRI1(addr))  "    CMP %1\n    JGE %a\n"  3

stmt: GEU1(reg,reg)  "    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JNC %a\n"  5
stmt: GEU1(reg,INDIRU1(addr))  "    CMP %1\n    JNC %a\n"  3

stmt: EQI2(INDIRI2(faddr),INDIRI2(faddr))  "    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JZ %a\n"  3
stmt: EQU2(INDIRU2(faddr),INDIRU2(faddr))  "    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JZ %a\n"  3
stmt: EQI2(reg,INDIRI2(faddr))  "    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JZ %a\n"  4
stmt: EQU2(reg,INDIRU2(faddr))  "    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JZ %a\n"  4
stmt: EQI2(reg,reg)  "    STA _tmp\n    POP\n    CMP _tmp\n    JZ %a\n"  10
stmt: EQU2(reg,reg)  "    STA _tmp\n    POP\n    CMP _tmp\n    JZ %a\n"  10

stmt: NEI2(INDIRI2(faddr),INDIRI2(faddr))  "    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNZ %a\n"  3
stmt: NEU2(INDIRU2(faddr),INDIRU2(faddr))  "    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNZ %a\n"  3
stmt: NEI2(reg,INDIRI2(faddr))  "    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNZ %a\n"  4
stmt: NEU2(reg,INDIRU2(faddr))  "    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNZ %a\n"  4
stmt: NEI2(reg,reg)  "    STA _tmp\n    POP\n    CMP _tmp\n    JNZ %a\n"  10
stmt: NEU2(reg,reg)  "    STA _tmp\n    POP\n    CMP _tmp\n    JNZ %a\n"  10

stmt: LTI2(INDIRI2(faddr),INDIRI2(faddr))  "    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JN %a\n"  3
stmt: LTU2(INDIRU2(faddr),INDIRU2(faddr))  "    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JC %a\n"  3
stmt: LTI2(reg,INDIRI2(faddr))  "    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JN %a\n"  4
stmt: LTU2(reg,INDIRU2(faddr))  "    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JC %a\n"  4
stmt: LTI2(reg,reg)  "    STA _tmp\n    POP\n    CMP _tmp\n    JN %a\n"  10
stmt: LTU2(reg,reg)  "    STA _tmp\n    POP\n    CMP _tmp\n    JC %a\n"  10

stmt: LEI2(INDIRI2(faddr),INDIRI2(faddr))  "    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JLE %a\n"  3
stmt: LEU2(INDIRU2(faddr),INDIRU2(faddr))  "    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JBE %a\n"  3
stmt: LEI2(reg,INDIRI2(faddr))  "    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JLE %a\n"  4
stmt: LEU2(reg,INDIRU2(faddr))  "    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JBE %a\n"  4
stmt: LEI2(reg,reg)  "    STA _tmp\n    POP\n    CMP _tmp\n    JLE %a\n"  10
stmt: LEU2(reg,reg)  "    STA _tmp\n    POP\n    CMP _tmp\n    JBE %a\n"  10

stmt: GTI2(INDIRI2(faddr),INDIRI2(faddr))  "    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JGT %a\n"  3
stmt: GTU2(INDIRU2(faddr),INDIRU2(faddr))  "    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JA %a\n"  3
stmt: GTI2(reg,INDIRI2(faddr))  "    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JGT %a\n"  4
stmt: GTU2(reg,INDIRU2(faddr))  "    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JA %a\n"  4
stmt: GTI2(reg,reg)  "    STA _tmp\n    POP\n    CMP _tmp\n    JGT %a\n"  10
stmt: GTU2(reg,reg)  "    STA _tmp\n    POP\n    CMP _tmp\n    JA %a\n"  10

stmt: GEI2(INDIRI2(faddr),INDIRI2(faddr))  "    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JGE %a\n"  3
stmt: GEU2(INDIRU2(faddr),INDIRU2(faddr))  "    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNC %a\n"  3
stmt: GEI2(reg,INDIRI2(faddr))  "    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JGE %a\n"  4
stmt: GEU2(reg,INDIRU2(faddr))  "    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNC %a\n"  4
stmt: GEI2(reg,reg)  "    STA _tmp\n    POP\n    CMP _tmp\n    JGE %a\n"  10
stmt: GEU2(reg,reg)  "    STA _tmp\n    POP\n    CMP _tmp\n    JNC %a\n"  10

stmt: LEI2(INDIRI2(faddr),con2)  "    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JLE %a\n"  2
stmt: LEU2(INDIRU2(faddr),con2)  "    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JBE %a\n"  2
stmt: LEI2(reg,con2)  "    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JLE %a\n"  3
stmt: LEU2(reg,con2)  "    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JBE %a\n"  3

stmt: GTI2(INDIRI2(faddr),con2)  "    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JGT %a\n"  2
stmt: GTU2(INDIRU2(faddr),con2)  "    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JA %a\n"  2
stmt: GTI2(reg,con2)  "    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JGT %a\n"  3
stmt: GTU2(reg,con2)  "    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JA %a\n"  3

stmt: GEI2(INDIRI2(faddr),con2)  "    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JGE %a\n"  2
stmt: GEU2(INDIRU2(faddr),con2)  "    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNC %a\n"  2
stmt: GEI2(reg,con2)  "    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JGE %a\n"  3
stmt: GEU2(reg,con2)  "    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNC %a\n"  3

stmt: LTI2(INDIRI2(faddr),con2)  "    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JN %a\n"  2
stmt: LTU2(INDIRU2(faddr),con2)  "    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JC %a\n"  2
stmt: LTI2(reg,con2)  "    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JN %a\n"  3
stmt: LTU2(reg,con2)  "    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JC %a\n"  3

stmt: EQI2(INDIRI2(faddr),con2)  "    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JZ %a\n"  2
stmt: EQU2(INDIRU2(faddr),con2)  "    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JZ %a\n"  2
stmt: EQI2(reg,con2)  "    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JZ %a\n"  3
stmt: EQU2(reg,con2)  "    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JZ %a\n"  3

stmt: NEI2(INDIRI2(faddr),con2)  "    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNZ %a\n"  2
stmt: NEU2(INDIRU2(faddr),con2)  "    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNZ %a\n"  2
stmt: NEI2(reg,con2)  "    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNZ %a\n"  3
stmt: NEU2(reg,con2)  "    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNZ %a\n"  3

stmt: ARGI1(reg)  "    PUSH\n"  1
stmt: ARGU1(reg)  "    PUSH\n"  1

stmt: ARGI2(reg)  "    PUSH\n"  1
stmt: ARGU2(reg)  "    PUSH\n"  1
stmt: ARGP2(reg)  "    PUSH\n"  1

stmt: ARGI4(reg)  "    PUSH\n    POP\n    PUSH\n    PUSH\n"  2
stmt: ARGU4(reg)  "    PUSH\n    POP\n    PUSH\n    PUSH\n"  2
stmt: ARGP4(reg)  "    PUSH\n    POP\n    PUSH\n    PUSH\n"  2

reg: CALLI1(addr)  "    CALL %0\n"  5
reg: CALLU1(addr)  "    CALL %0\n"  5

reg: CALLI2(addr)  "    CALL %0\n"  5
reg: CALLU2(addr)  "    CALL %0\n"  5
reg: CALLP2(addr)  "    CALL %0\n"  5

reg: CALLI4(addr)  "    CALL %0\n"  8
reg: CALLU4(addr)  "    CALL %0\n"  8
reg: CALLP4(addr)  "    CALL %0\n"  8

stmt: CALLV(addr)  "    CALL %0\n"  5

stmt: RETI1(reg)  "; ret - value in AC\n"  0
stmt: RETU1(reg)  "; ret - value in AC\n"  0

stmt: RETI2(reg)  "; ret - value in AC\n"  0
stmt: RETU2(reg)  "; ret - value in AC\n"  0
stmt: RETP2(reg)  "; ret - value in AC\n"  0

stmt: RETI4(reg)  "; ret - 32-bit value in stack\n"  0
stmt: RETU4(reg)  "; ret - 32-bit value in stack\n"  0
stmt: RETP4(reg)  "; ret - 32-bit value in stack\n"  0

stmt: RETV  "; ret void\n"  0

reg: LOADI1(reg)  ""  move(a)
reg: LOADU1(reg)  ""  move(a)
reg: LOADI2(reg)  ""  move(a)
reg: LOADU2(reg)  ""  move(a)
reg: LOADP2(reg)  ""  move(a)
reg: LOADI4(reg)  ""  move(a)
reg: LOADU4(reg)  ""  move(a)
reg: LOADP4(reg)  ""  move(a)

stmt: reg  ""

%%

static Symbol rmap(int opk) {
    return intregw;
}

static void blkfetch(int k, int off, int reg, int tmp) { }
static void blkstore(int k, int off, int reg, int tmp) { }
static void blkloop(int dreg, int doff, int sreg, int soff, int size, int tmps[]) { }

static void progbeg(int argc, char *argv[]) {
    int i;

    for (i = 1; i < argc; i++) {
    }

    /* Register AC (primary accumulator) */
    intreg[REG_AC] = mkreg("AC", REG_AC, 1, IREG);
    /* Register X (can hold temporaries) */
    intreg[REG_X] = xreg = mkreg("X", REG_X, 1, IREG);
    /* Register Y (can hold temporaries) */
    intreg[REG_Y] = yreg = mkreg("Y", REG_Y, 1, IREG);

    intregw = mkwildcard(intreg);

    /* AC is primary, X and Y for indexing/special purposes */
    tmask[IREG] = 0x07;
    vmask[IREG] = 0;

    print("; NEANDER-X 16-bit Assembly\n");
    print("; Generated by LCC (native 16-bit target)\n");
    print("\n");
    print("; Memory layout:\n");
    print("; 0x0000-0x002F: Runtime variables (below stack area)\n");
    print("; 0x0030-0x00FF: Stack (SP starts at 0x00FF, grows down)\n");
    print("; 0x0100+: Code\n");
    print("\n");
    print("; Jump to startup code at 0x0100\n");
    print("    .org 0x0000\n");
    print("    JMP _start\n");
    print("\n");
    print("; Runtime variables\n");
    print("_tmp:     .word 0     ; General purpose 16-bit temp\n");
    print("_tmp_hi:  .word 0     ; For 32-bit ops (high word)\n");
    print("_tmp2:    .word 0     ; Second 16-bit temp\n");
    print("_tmp2_hi: .word 0     ; For 32-bit ops (high word)\n");
    print("_mask_ff: .word 0x00FF ; Mask for 8-bit values\n");
    {
        int i;
        for (i = 0; i < 16; i++) {
            print("_vreg%d:   .word 0     ; VREG spill slot %d\n", i, i);
        }
    }
    print("\n");
    print("; Code section at 0x0100 (above stack area)\n");
    print("    .org 0x0100\n");
    print("_start:\n");
    print("    CALL _main\n");
    print("    HLT\n");
    print("\n");
}

static void progend(void) {
    print("\n");
    print("; End of program\n");
    print("    HLT\n");
}

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

static void defconst(int suffix, int size, Value v) {
    switch (size) {
    case 1:
        print("    .byte %d\n", v.u & 0xFF);
        break;
    case 2:
        /* 16-bit value in little-endian */
        print("    .byte %d\n", v.u & 0xFF);
        print("    .byte %d\n", (v.u >> 8) & 0xFF);
        break;
    case 4:
        /* 32-bit value in little-endian (for long type) */
        print("    .byte %d\n", v.u & 0xFF);
        print("    .byte %d\n", (v.u >> 8) & 0xFF);
        print("    .byte %d\n", (v.u >> 16) & 0xFF);
        print("    .byte %d\n", (v.u >> 24) & 0xFF);
        break;
    default:
        assert(0);
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

static void space(int n) {
    print("    .space %d\n", n);
}

static void local(Symbol p) {
    /* Ensure 2-byte alignment for 16-bit architecture */
    offset = roundup(offset + p->type->size, p->type->align < 2 ? 2 : p->type->align);
    p->x.offset = -offset;
    p->x.name = stringf("%d", -offset);
}

/* Number of VREGs to save/restore for callee-save (for recursive function support) */
#define CALLEE_SAVE_VREGS 4

static void function(Symbol f, Symbol caller[], Symbol callee[], int ncalls) {
    int i;
    int param_offset;
    int save_vregs = (ncalls > 0) ? CALLEE_SAVE_VREGS : 0;

    /* Reset VREG slot mapping for each function */
    next_vreg_slot = 0;
    for (i = 0; i < MAX_VREG_SLOTS; i++) {
        vreg_symbols[i] = NULL;
    }

    print("\n; Function: %s\n", f->name);
    print("%s:\n", f->x.name);

    print("    ; Prologue\n");
    print("    PUSH_FP\n");

    /* Callee-save: preserve VREGs if function makes calls */
    if (save_vregs > 0) {
        print("    ; Callee-save %d VREGs\n", save_vregs);
        for (i = 0; i < save_vregs; i++) {
            print("    PUSH_ADDR _vreg%d\n", i);
        }
    }

    print("    TSF\n");

    usedmask[IREG] = 0;
    freemask[IREG] = tmask[IREG];

    /* Parameters start at FP+4 + saved_vregs*2 (after saved FP, saved VREGs, and return address) */
    param_offset = 4 + save_vregs * 2;
    for (i = 0; callee[i]; i++) {
        Symbol p = callee[i];
        Symbol q = caller[i];
        p->x.offset = q->x.offset = param_offset;
        p->x.name = q->x.name = stringf("%d", param_offset);
        p->sclass = q->sclass = AUTO;
        /* 2-byte alignment for 16-bit architecture */
        param_offset += roundup(q->type->size, 2);
    }

    offset = maxoffset = 0;
    gencode(caller, callee);

    if (maxoffset > 0) {
        print("    ; Allocate %d bytes for locals\n", maxoffset);
        for (i = 0; i < maxoffset; i++) {
            print("    LDI 0\n");
            print("    PUSH\n");
        }
    }

    emitcode();

    print("    ; Epilogue\n");
    print("    TFS\n");

    /* Callee-restore: restore VREGs in reverse order */
    if (save_vregs > 0) {
        print("    ; Callee-restore %d VREGs\n", save_vregs);
        for (i = save_vregs - 1; i >= 0; i--) {
            print("    POP_ADDR _vreg%d\n", i);
        }
    }

    print("    POP_FP\n");
    print("    RET\n");
}

static void emit2(Node p) {
    /* Handle VREG spill/reload for accumulator architecture */
    /* Each unique VREG Symbol gets its own dedicated memory slot */
    int op = specific(p->op);
    Symbol reg, reg1, reg2;
    int slot, slot1, slot2;
    Node left, right;

    /* VREG terminal opcode = 711 */
    #define VREG_OP 711
    #define IS_VREG_NODE(n) ((n) && (n)->op == VREG_OP)

    switch (op) {
    case ASGN+I:
    case ASGN+U:
    case ASGN+P:
        /* Write to VREG - need to load source value first, then store */
        if (IS_VREG_NODE(LEFT_CHILD(p))) {
            reg = LEFT_CHILD(p)->syms[0];
            slot = get_vreg_slot(reg);
            right = RIGHT_CHILD(p);

            /* Check source type and emit appropriate load */
            if (right) {
                int right_op = generic(right->op);
                /* If source is INDIR (memory load), emit LDA */
                if (right_op == INDIR) {
                    Node addr = LEFT_CHILD(right);
                    if (addr) {
                        int addr_op = specific(addr->op);
                        /* ADDRFP2 = 2327 & 0x3FF = 279, but check generic ADDRF */
                        if (generic(addr->op) == ADDRF) {
                            /* Load from frame pointer relative address */
                            print("    LDA %d,FP\n", addr->syms[0]->x.offset);
                        } else if (generic(addr->op) == ADDRL) {
                            /* Load from local variable */
                            print("    LDA %d,FP\n", addr->syms[0]->x.offset);
                        } else if (generic(addr->op) == ADDRG) {
                            /* Load from global */
                            print("    LDA %s\n", addr->syms[0]->x.name);
                        }
                    }
                }
                /* If source is already a VREG read, it's handled by INDIR case in emit2 */
            }
            print("    STA _vreg%d\n", slot);
        }
        break;
    case INDIR+I:
    case INDIR+U:
    case INDIR+P:
        /* Read from VREG - load from dedicated memory slot */
        if (IS_VREG_NODE(LEFT_CHILD(p))) {
            reg = LEFT_CHILD(p)->syms[0];
            slot = get_vreg_slot(reg);
            print("    LDA _vreg%d\n", slot);
        }
        break;
    case ADD+I:
    case ADD+U:
    case ADD+P:
        /* Handle VREG + VREG or VREG + const */
        left = LEFT_CHILD(p);
        right = RIGHT_CHILD(p);
        if (left && right) {
            /* Check for vreg + vreg */
            if (generic(left->op) == INDIR && IS_VREG_NODE(LEFT_CHILD(left)) &&
                generic(right->op) == INDIR && IS_VREG_NODE(LEFT_CHILD(right))) {
                /* vreg + vreg: load first to temp, load second, add */
                reg1 = LEFT_CHILD(left)->syms[0];
                reg2 = LEFT_CHILD(right)->syms[0];
                slot1 = get_vreg_slot(reg1);
                slot2 = get_vreg_slot(reg2);
                print("    LDA _vreg%d\n", slot1);
                print("    STA _tmp\n");
                print("    LDA _vreg%d\n", slot2);
                print("    ADD _tmp\n");
            }
            /* Check for vreg + const */
            else if (generic(left->op) == INDIR && IS_VREG_NODE(LEFT_CHILD(left)) &&
                     generic(right->op) == CNST) {
                reg1 = LEFT_CHILD(left)->syms[0];
                slot1 = get_vreg_slot(reg1);
                print("    LDA _vreg%d\n", slot1);
                print("    STA _tmp\n");
                print("    LDI %d\n", right->syms[0]->u.c.v.i);
                print("    ADD _tmp\n");
            }
        }
        break;
    case MUL+I:
    case MUL+U:
        /* Handle VREG * VREG */
        left = LEFT_CHILD(p);
        right = RIGHT_CHILD(p);
        if (left && right) {
            /* Check for vreg * vreg */
            if (generic(left->op) == INDIR && IS_VREG_NODE(LEFT_CHILD(left)) &&
                generic(right->op) == INDIR && IS_VREG_NODE(LEFT_CHILD(right))) {
                /* vreg * vreg: load second to X, load first to AC, multiply */
                reg1 = LEFT_CHILD(left)->syms[0];
                reg2 = LEFT_CHILD(right)->syms[0];
                slot1 = get_vreg_slot(reg1);
                slot2 = get_vreg_slot(reg2);
                print("    LDA _vreg%d\n", slot2);
                print("    TAX\n");
                print("    LDA _vreg%d\n", slot1);
                print("    MUL\n");
            }
        }
        break;
    case SUB+I:
    case SUB+U:
        /* Handle VREG - VREG */
        left = LEFT_CHILD(p);
        right = RIGHT_CHILD(p);
        if (left && right) {
            /* Check for vreg - vreg */
            if (generic(left->op) == INDIR && IS_VREG_NODE(LEFT_CHILD(left)) &&
                generic(right->op) == INDIR && IS_VREG_NODE(LEFT_CHILD(right))) {
                /* vreg - vreg: load subtrahend to temp, load minuend to AC, subtract */
                reg1 = LEFT_CHILD(left)->syms[0];  /* minuend */
                reg2 = LEFT_CHILD(right)->syms[0]; /* subtrahend */
                slot1 = get_vreg_slot(reg1);
                slot2 = get_vreg_slot(reg2);
                print("    LDA _vreg%d\n", slot2);  /* load subtrahend */
                print("    STA _tmp\n");
                print("    LDA _vreg%d\n", slot1);  /* load minuend */
                print("    SUB _tmp\n");           /* AC = minuend - subtrahend */
            }
        }
        break;
    case BXOR+I:
    case BXOR+U:
        /* Handle VREG ^ VREG */
        left = LEFT_CHILD(p);
        right = RIGHT_CHILD(p);
        if (left && right) {
            if (generic(left->op) == INDIR && IS_VREG_NODE(LEFT_CHILD(left)) &&
                generic(right->op) == INDIR && IS_VREG_NODE(LEFT_CHILD(right))) {
                reg1 = LEFT_CHILD(left)->syms[0];
                reg2 = LEFT_CHILD(right)->syms[0];
                slot1 = get_vreg_slot(reg1);
                slot2 = get_vreg_slot(reg2);
                print("    LDA _vreg%d\n", slot1);
                print("    STA _tmp\n");
                print("    LDA _vreg%d\n", slot2);
                print("    XOR _tmp\n");
            }
        }
        break;
    case BAND+I:
    case BAND+U:
        /* Handle VREG & VREG */
        left = LEFT_CHILD(p);
        right = RIGHT_CHILD(p);
        if (left && right) {
            if (generic(left->op) == INDIR && IS_VREG_NODE(LEFT_CHILD(left)) &&
                generic(right->op) == INDIR && IS_VREG_NODE(LEFT_CHILD(right))) {
                reg1 = LEFT_CHILD(left)->syms[0];
                reg2 = LEFT_CHILD(right)->syms[0];
                slot1 = get_vreg_slot(reg1);
                slot2 = get_vreg_slot(reg2);
                print("    LDA _vreg%d\n", slot1);
                print("    STA _tmp\n");
                print("    LDA _vreg%d\n", slot2);
                print("    AND _tmp\n");
            }
        }
        break;
    case BOR+I:
    case BOR+U:
        /* Handle VREG | VREG */
        left = LEFT_CHILD(p);
        right = RIGHT_CHILD(p);
        if (left && right) {
            if (generic(left->op) == INDIR && IS_VREG_NODE(LEFT_CHILD(left)) &&
                generic(right->op) == INDIR && IS_VREG_NODE(LEFT_CHILD(right))) {
                reg1 = LEFT_CHILD(left)->syms[0];
                reg2 = LEFT_CHILD(right)->syms[0];
                slot1 = get_vreg_slot(reg1);
                slot2 = get_vreg_slot(reg2);
                print("    LDA _vreg%d\n", slot1);
                print("    STA _tmp\n");
                print("    LDA _vreg%d\n", slot2);
                print("    OR _tmp\n");
            }
        }
        break;
    }
}

static void doarg(Node p) {
    /* Track argument bytes being pushed (for mkactual) */
    mkactual(2, roundup(p->syms[0]->u.c.v.i, 2));
}

static void target(Node p) {
    switch (specific(p->op)) {
    case CALL+I:
    case CALL+U:
    case CALL+P:
    case CALL+V:
        setreg(p, intreg[REG_AC]);
        /* docall() in gen.c sets p->syms[0] to intconst(argoffset) */
        break;
    case RET+I:
    case RET+U:
    case RET+P:
        rtarget(p, 0, intreg[REG_AC]);
        break;
    }
}

static void clobber(Node p) {
    /* Stack-based machine - no clobbering needed */
}

Interface neanderxIR = {
    1, 1, 0,  /* char:        1 byte, 1-byte align */
    2, 2, 0,  /* short:       2 bytes, 2-byte align (16-bit native) */
    2, 2, 0,  /* int:         2 bytes, 2-byte align (16-bit native) */
    4, 2, 0,  /* long:        4 bytes, 2-byte align (32-bit) */
    4, 2, 0,  /* long long:   4 bytes, 2-byte align (32-bit) */
    0, 1, 1,  /* float:       not supported */
    0, 1, 1,  /* double:      not supported */
    0, 1, 1,  /* long double: not supported */
    2, 2, 0,  /* pointer:     2 bytes, 2-byte align (16-bit address) */
    0, 2, 0,  /* struct:      2-byte alignment */

    1,
    0,
    0,
    1,
    0,
    0,
    1,

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
