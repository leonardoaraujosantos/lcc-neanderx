%{
/* =============================================================================
 * NEANDER-X Backend for LCC
 * =============================================================================
 *
 * This is an LCC backend for the NEANDER-X 8-bit educational processor.
 *
 * NEANDER-X Characteristics:
 * - 8-bit data width
 * - 16-bit address space (64KB via SPI SRAM)
 * - Accumulator-based architecture
 * - Registers: AC (8-bit), X (8-bit), Y (8-bit), FP (16-bit), SP (16-bit), PC (16-bit)
 * - Three condition flags: N (Negative), Z (Zero), C (Carry)
 * - Hardware MUL, DIV, MOD instructions
 * - ADC/SBC for multi-byte arithmetic
 * - Frame pointer support for C-style stack frames
 * - Indexed addressing modes with X, Y, FP
 *
 * Type mapping:
 * - char:    1 byte (native)
 * - short:   1 byte (8-bit processor limitation)
 * - int:     1 byte (8-bit native)
 * - long:    2 bytes (using ADC/SBC)
 * - pointer: 2 bytes (16-bit address space)
 * - float:   not supported (out-of-line)
 *
 * Calling convention:
 * - Arguments pushed right-to-left on stack
 * - Return value in AC (8-bit) or AC:Y (16-bit, Y=high byte)
 * - Caller cleans up arguments
 * - FP-relative addressing for parameters and locals
 *
 * =============================================================================
 */

#include "c.h"

#define NODEPTR_TYPE Node
#define OP_LABEL(p) ((p)->op)
#define LEFT_CHILD(p) ((p)->kids[0])
#define RIGHT_CHILD(p) ((p)->kids[1])
#define STATE_LABEL(p) ((p)->x.state)

/* Register indices */
enum { REG_AC=0, REG_X=1, REG_Y=2, REG_MAX=3 };

#define IREG 1    /* Integer register class */

static Symbol intreg[32];  /* Integer register array */
static Symbol intregw;     /* Wildcard for integer registers */

static int cseg;           /* Current segment */
static int tmpcount;       /* Temporary variable counter */

static char rcsid[] = "$Id: neanderx.md $";

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

reg: con2  "    LDI lo(%0)\n    PUSH\n    LDI hi(%0)\n"  4

reg: con4  "    LDI %0\n"  1

addr: ADDRGP2  "%a"
addr: ADDRFP2  "%a"
addr: ADDRLP2  "%a"

addr: ADDRGP4  "%a"
addr: ADDRFP4  "%a"
addr: ADDRLP4  "%a"

reg: INDIRI1(addr)  "    LDA %0\n"  2
reg: INDIRU1(addr)  "    LDA %0\n"  2
reg: INDIRI4(addr)  "    LDA %0\n"  2
reg: INDIRU4(addr)  "    LDA %0\n"  2

reg: INDIRI1(ADDRFP2)  "    LDA_FP %a\n"  2
reg: INDIRU1(ADDRFP2)  "    LDA_FP %a\n"  2
reg: INDIRI1(ADDRLP2)  "    LDA_FP %a\n"  2
reg: INDIRU1(ADDRLP2)  "    LDA_FP %a\n"  2

reg: INDIRI2(addr)  "    LDA %0\n    PUSH\n    LDA %0+1\n"  4
reg: INDIRU2(addr)  "    LDA %0\n    PUSH\n    LDA %0+1\n"  4
reg: INDIRP2(addr)  "    LDA %0\n    PUSH\n    LDA %0+1\n"  4

reg: INDIRI2(ADDRFP2)  "    LDA_FP %a\n    PUSH\n    LDA_FP %a+1\n"  4
reg: INDIRU2(ADDRFP2)  "    LDA_FP %a\n    PUSH\n    LDA_FP %a+1\n"  4
reg: INDIRP2(ADDRFP2)  "    LDA_FP %a\n    PUSH\n    LDA_FP %a+1\n"  4

stmt: ASGNI1(addr,reg)  "    STA %0\n"  2
stmt: ASGNU1(addr,reg)  "    STA %0\n"  2

stmt: ASGNI1(ADDRFP2,reg)  "    STA_FP %a\n"  2
stmt: ASGNU1(ADDRFP2,reg)  "    STA_FP %a\n"  2
stmt: ASGNI1(ADDRLP2,reg)  "    STA_FP %a\n"  2
stmt: ASGNU1(ADDRLP2,reg)  "    STA_FP %a\n"  2

stmt: ASGNI2(addr,reg)  "    STA %0\n    POP\n    STA %0+1\n"  4
stmt: ASGNU2(addr,reg)  "    STA %0\n    POP\n    STA %0+1\n"  4
stmt: ASGNP2(addr,reg)  "    STA %0\n    POP\n    STA %0+1\n"  4

stmt: ASGNI2(ADDRFP2,reg)  "    STA_FP %a\n    POP\n    STA_FP %a+1\n"  4
stmt: ASGNU2(ADDRFP2,reg)  "    STA_FP %a\n    POP\n    STA_FP %a+1\n"  4
stmt: ASGNP2(ADDRFP2,reg)  "    STA_FP %a\n    POP\n    STA_FP %a+1\n"  4

reg: INDIRI1(ADDI2(addr,reg))  "    TAX\n    LDA_X %0\n"  3
reg: INDIRU1(ADDI2(addr,reg))  "    TAX\n    LDA_X %0\n"  3

stmt: ASGNI1(ADDI2(addr,reg),reg)  "    PUSH\n    TAX\n    POP\n    STA_X %0\n"  5
stmt: ASGNU1(ADDI2(addr,reg),reg)  "    PUSH\n    TAX\n    POP\n    STA_X %0\n"  5

reg: ADDI1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    ADD _tmp\n"  5
reg: ADDU1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    ADD _tmp\n"  5

reg: ADDI1(reg,INDIRI1(addr))  "    ADD %1\n"  2
reg: ADDU1(reg,INDIRU1(addr))  "    ADD %1\n"  2

reg: ADDI1(reg,conN)  "    INC\n"  1
reg: ADDU1(reg,conN)  "    INC\n"  1

reg: SUBI1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    SUB _tmp\n"  5
reg: SUBU1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    SUB _tmp\n"  5

reg: SUBI1(reg,INDIRI1(addr))  "    SUB %1\n"  2
reg: SUBU1(reg,INDIRU1(addr))  "    SUB %1\n"  2

reg: SUBI1(reg,conN)  "    DEC\n"  1
reg: SUBU1(reg,conN)  "    DEC\n"  1

reg: NEGI1(reg)  "    NEG\n"  1

reg: ADDI2(reg,reg)  "    STA _tmp_lo\n    POP\n    STA _tmp_hi\n    POP\n    STA _t2_hi\n    POP\n    ADD _tmp_lo\n    PUSH\n    LDA _tmp_hi\n    ADC _t2_hi\n"  12
reg: ADDU2(reg,reg)  "    STA _tmp_lo\n    POP\n    STA _tmp_hi\n    POP\n    STA _t2_hi\n    POP\n    ADD _tmp_lo\n    PUSH\n    LDA _tmp_hi\n    ADC _t2_hi\n"  12

reg: SUBI2(reg,reg)  "    STA _tmp_lo\n    POP\n    STA _tmp_hi\n    POP\n    STA _t2_hi\n    POP\n    LDI 0\n    ADD _zero\n    POP\n    SUB _tmp_lo\n    PUSH\n    LDA _t2_hi\n    SBC _tmp_hi\n"  15
reg: SUBU2(reg,reg)  "    STA _tmp_lo\n    POP\n    STA _tmp_hi\n    POP\n    STA _t2_hi\n    POP\n    LDI 0\n    ADD _zero\n    POP\n    SUB _tmp_lo\n    PUSH\n    LDA _t2_hi\n    SBC _tmp_hi\n"  15

reg: ADDI4(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    ADD _tmp\n"  5
reg: ADDU4(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    ADD _tmp\n"  5

reg: SUBI4(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    SUB _tmp\n"  5
reg: SUBU4(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    SUB _tmp\n"  5

reg: MULI1(reg,reg)  "    PUSH\n    TAX\n    POP\n    MUL\n"  5
reg: MULU1(reg,reg)  "    PUSH\n    TAX\n    POP\n    MUL\n"  5

reg: DIVI1(reg,reg)  "    PUSH\n    TAX\n    POP\n    DIV\n"  5
reg: DIVU1(reg,reg)  "    PUSH\n    TAX\n    POP\n    DIV\n"  5

reg: MODI1(reg,reg)  "    PUSH\n    TAX\n    POP\n    MOD\n"  5
reg: MODU1(reg,reg)  "    PUSH\n    TAX\n    POP\n    MOD\n"  5

reg: BANDI1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    AND _tmp\n"  5
reg: BANDU1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    AND _tmp\n"  5

reg: BANDI1(reg,INDIRI1(addr))  "    AND %1\n"  2
reg: BANDU1(reg,INDIRU1(addr))  "    AND %1\n"  2

reg: BORI1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    OR _tmp\n"  5
reg: BORU1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    OR _tmp\n"  5

reg: BORI1(reg,INDIRI1(addr))  "    OR %1\n"  2
reg: BORU1(reg,INDIRU1(addr))  "    OR %1\n"  2

reg: BXORI1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    XOR _tmp\n"  5
reg: BXORU1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    XOR _tmp\n"  5

reg: BXORI1(reg,INDIRI1(addr))  "    XOR %1\n"  2
reg: BXORU1(reg,INDIRU1(addr))  "    XOR %1\n"  2

reg: BCOMI1(reg)  "    NOT\n"  1
reg: BCOMU1(reg)  "    NOT\n"  1

reg: LSHI1(reg,conN)  "    SHL\n"  1
reg: LSHU1(reg,conN)  "    SHL\n"  1

reg: RSHU1(reg,conN)  "    SHR\n"  1
reg: RSHI1(reg,conN)  "    ASR\n"  1

reg: LSHI1(reg,reg)  "    PUSH\n    TAX\n    POP\n_shl_%a:\n    TXA\n    JZ _shld_%a\n    SHL\n    DEX\n    JMP _shl_%a\n_shld_%a:\n"  10
reg: LSHU1(reg,reg)  "    PUSH\n    TAX\n    POP\n_shl_%a:\n    TXA\n    JZ _shld_%a\n    SHL\n    DEX\n    JMP _shl_%a\n_shld_%a:\n"  10

reg: RSHU1(reg,reg)  "    PUSH\n    TAX\n    POP\n_shr_%a:\n    TXA\n    JZ _shrd_%a\n    SHR\n    DEX\n    JMP _shr_%a\n_shrd_%a:\n"  10
reg: RSHI1(reg,reg)  "    PUSH\n    TAX\n    POP\n_asr_%a:\n    TXA\n    JZ _asrd_%a\n    ASR\n    DEX\n    JMP _asr_%a\n_asrd_%a:\n"  10

reg: CVII1(reg)  "# cvii1 - truncate to 1 byte\n"  0
reg: CVIU1(reg)  "# cviu1\n"  0
reg: CVUI1(reg)  "# cvui1\n"  0
reg: CVUU1(reg)  "# cvuu1\n"  0

reg: CVII2(reg)  "    TAY\n    LDI 0\n    TYA\n    JN _sx_%a\n    LDI 0\n    JMP _sxd_%a\n_sx_%a:\n    LDI 0xFF\n_sxd_%a:\n    PUSH\n    TYA\n"  8
reg: CVIU2(reg)  "    PUSH\n    LDI 0\n"  2
reg: CVUI2(reg)  "    PUSH\n    LDI 0\n"  2
reg: CVUU2(reg)  "    PUSH\n    LDI 0\n"  2

reg: CVII1(INDIRI2(addr))  "    LDA %0\n"  2
reg: CVUU1(INDIRU2(addr))  "    LDA %0\n"  2

reg: CVPU2(reg)  "# cvpu2\n"  0
reg: CVUP2(reg)  "# cvup2\n"  0

reg: CVII4(reg)  "# cvii4 - extend to 4 byte\n"  0
reg: CVIU4(reg)  "# cviu4\n"  0
reg: CVUI4(reg)  "# cvui4\n"  0
reg: CVUU4(reg)  "# cvuu4\n"  0
reg: CVPU4(reg)  "# cvpu4\n"  0
reg: CVUP4(reg)  "# cvup4\n"  0

stmt: LABELV  "%a:\n"

stmt: JUMPV(addr)  "    JMP %0\n"  1
stmt: JUMPV(reg)   "    JMP %0\n"  10

stmt: EQI1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    CMP _tmp\n    JZ %a\n"  6
stmt: EQU1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    CMP _tmp\n    JZ %a\n"  6

stmt: EQI1(reg,INDIRI1(addr))  "    CMP %1\n    JZ %a\n"  3
stmt: EQU1(reg,INDIRU1(addr))  "    CMP %1\n    JZ %a\n"  3

stmt: NEI1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    CMP _tmp\n    JNZ %a\n"  6
stmt: NEU1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    CMP _tmp\n    JNZ %a\n"  6

stmt: NEI1(reg,INDIRI1(addr))  "    CMP %1\n    JNZ %a\n"  3
stmt: NEU1(reg,INDIRU1(addr))  "    CMP %1\n    JNZ %a\n"  3

stmt: LTI1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    CMP _tmp\n    JN %a\n"  6
stmt: LTI1(reg,INDIRI1(addr))  "    CMP %1\n    JN %a\n"  3

stmt: LTU1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    CMP _tmp\n    JC %a\n"  6
stmt: LTU1(reg,INDIRU1(addr))  "    CMP %1\n    JC %a\n"  3

stmt: LEI1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    CMP _tmp\n    JLE %a\n"  6
stmt: LEI1(reg,INDIRI1(addr))  "    CMP %1\n    JLE %a\n"  3

stmt: LEU1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    CMP _tmp\n    JBE %a\n"  6
stmt: LEU1(reg,INDIRU1(addr))  "    CMP %1\n    JBE %a\n"  3

stmt: GTI1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    CMP _tmp\n    JGT %a\n"  6
stmt: GTI1(reg,INDIRI1(addr))  "    CMP %1\n    JGT %a\n"  3

stmt: GTU1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    CMP _tmp\n    JA %a\n"  6
stmt: GTU1(reg,INDIRU1(addr))  "    CMP %1\n    JA %a\n"  3

stmt: GEI1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    CMP _tmp\n    JGE %a\n"  6
stmt: GEI1(reg,INDIRI1(addr))  "    CMP %1\n    JGE %a\n"  3

stmt: GEU1(reg,reg)  "    PUSH\n    STA _tmp\n    POP\n    CMP _tmp\n    JNC %a\n"  6
stmt: GEU1(reg,INDIRU1(addr))  "    CMP %1\n    JNC %a\n"  3

stmt: ARGI1(reg)  "    PUSH\n"  1
stmt: ARGU1(reg)  "    PUSH\n"  1

stmt: ARGI2(reg)  "    PUSH\n"  2
stmt: ARGU2(reg)  "    PUSH\n"  2
stmt: ARGP2(reg)  "    PUSH\n"  2

reg: CALLI1(addr)  "    CALL %0\n"  5
reg: CALLU1(addr)  "    CALL %0\n"  5

reg: CALLI2(addr)  "    CALL %0\n    PUSH\n    TYA\n"  6
reg: CALLU2(addr)  "    CALL %0\n    PUSH\n    TYA\n"  6
reg: CALLP2(addr)  "    CALL %0\n    PUSH\n    TYA\n"  6

stmt: CALLV(addr)  "    CALL %0\n"  5

stmt: RETI1(reg)  "# ret\n"  0
stmt: RETU1(reg)  "# ret\n"  0

stmt: RETI2(reg)  "    TAY\n    POP\n"  2
stmt: RETU2(reg)  "    TAY\n    POP\n"  2
stmt: RETP2(reg)  "    TAY\n    POP\n"  2

stmt: RETI4(reg)  "# ret\n"  0
stmt: RETU4(reg)  "# ret\n"  0
stmt: RETP4(reg)  "# ret\n"  0

stmt: RETV  "# ret\n"  0

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

    intreg[REG_AC] = mkreg("AC", REG_AC, 1, IREG);

    intregw = mkwildcard(intreg);

    tmask[IREG] = 0x01;
    vmask[IREG] = 0;

    print("; NEANDER-X Assembly\n");
    print("; Generated by LCC\n");
    print("\n");
    print("; Runtime variables\n");
    print("    .org 0x0000\n");
    print("_tmp:    .byte 0\n");
    print("_tmp_lo: .byte 0\n");
    print("_tmp_hi: .byte 0\n");
    print("_t2_hi:  .byte 0\n");
    print("_zero:   .byte 0\n");
    print("\n");
    print("; Code section\n");
    print("    .org 0x0100\n");
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
        print("    .byte %d\n", v.u & 0xFF);
        print("    .byte %d\n", (v.u >> 8) & 0xFF);
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
    offset = roundup(offset + p->type->size, p->type->align);
    p->x.offset = -offset;
    p->x.name = stringf("%d", -offset);
}

static void function(Symbol f, Symbol caller[], Symbol callee[], int ncalls) {
    int i;
    int param_offset;

    print("\n; Function: %s\n", f->name);
    print("%s:\n", f->x.name);

    print("    ; Prologue\n");
    print("    PUSH_FP\n");
    print("    TSF\n");

    usedmask[IREG] = 0;
    freemask[IREG] = tmask[IREG];

    param_offset = 4;
    for (i = 0; callee[i]; i++) {
        Symbol p = callee[i];
        Symbol q = caller[i];
        p->x.offset = q->x.offset = param_offset;
        p->x.name = q->x.name = stringf("%d", param_offset);
        p->sclass = q->sclass = AUTO;
        param_offset += roundup(q->type->size, 1);
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
    print("    POP_FP\n");
    print("    RET\n");
}

static void emit2(Node p) {
}

static void doarg(Node p) {
}

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
        spill(0xFF, IREG, p);
        break;
    }
}

Interface neanderxIR = {
    1, 1, 0,
    1, 1, 0,
    1, 1, 0,
    2, 1, 0,
    2, 1, 0,
    0, 1, 1,
    0, 1, 1,
    0, 1, 1,
    2, 1, 0,
    0, 1, 0,

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
