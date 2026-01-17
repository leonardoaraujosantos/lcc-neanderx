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

/*
generated at Fri Jan 16 22:52:33 2026
by $Id$
*/
static void _kids(NODEPTR_TYPE, int, NODEPTR_TYPE[]);
static void _label(NODEPTR_TYPE);
static int _rule(void*, int);

#define _stmt_NT 1
#define _reg_NT 2
#define _con2_NT 3
#define _con1_NT 4
#define _con4_NT 5
#define _conN_NT 6
#define _addr_NT 7
#define _faddr_NT 8

static char *_ntname[] = {
	0,
	"stmt",
	"reg",
	"con2",
	"con1",
	"con4",
	"conN",
	"addr",
	"faddr",
	0
};

struct _state {
	short cost[9];
	struct {
		unsigned int _stmt:8;
		unsigned int _reg:8;
		unsigned int _con2:2;
		unsigned int _con1:2;
		unsigned int _con4:2;
		unsigned int _conN:2;
		unsigned int _addr:3;
		unsigned int _faddr:3;
	} rule;
};

static short _nts_0[] = { 0 };
static short _nts_1[] = { _con2_NT, 0 };
static short _nts_2[] = { _reg_NT, 0 };
static short _nts_3[] = { _con1_NT, 0 };
static short _nts_4[] = { _con4_NT, 0 };
static short _nts_5[] = { _faddr_NT, 0 };
static short _nts_6[] = { _faddr_NT, _reg_NT, 0 };
static short _nts_7[] = { _addr_NT, 0 };
static short _nts_8[] = { _addr_NT, _reg_NT, 0 };
static short _nts_9[] = { _reg_NT, _addr_NT, 0 };
static short _nts_10[] = { _addr_NT, _reg_NT, _reg_NT, 0 };
static short _nts_11[] = { _reg_NT, _addr_NT, _reg_NT, 0 };
static short _nts_12[] = { _addr_NT, _addr_NT, 0 };
static short _nts_13[] = { _reg_NT, _reg_NT, 0 };
static short _nts_14[] = { _reg_NT, _conN_NT, 0 };
static short _nts_15[] = { _faddr_NT, _con2_NT, 0 };
static short _nts_16[] = { _faddr_NT, _faddr_NT, 0 };
static short _nts_17[] = { _addr_NT, _con2_NT, 0 };
static short _nts_18[] = { _reg_NT, _faddr_NT, 0 };
static short _nts_19[] = { _reg_NT, _con2_NT, 0 };

static short *_nts[] = {
	0,	/* 0 */
	_nts_0,	/* 1 */
	_nts_0,	/* 2 */
	_nts_0,	/* 3 */
	_nts_0,	/* 4 */
	_nts_0,	/* 5 */
	_nts_0,	/* 6 */
	_nts_0,	/* 7 */
	_nts_0,	/* 8 */
	_nts_0,	/* 9 */
	_nts_0,	/* 10 */
	_nts_0,	/* 11 */
	_nts_1,	/* 12 */
	_nts_1,	/* 13 */
	_nts_0,	/* 14 */
	_nts_0,	/* 15 */
	_nts_2,	/* 16 */
	_nts_2,	/* 17 */
	_nts_2,	/* 18 */
	_nts_2,	/* 19 */
	_nts_2,	/* 20 */
	_nts_2,	/* 21 */
	_nts_2,	/* 22 */
	_nts_2,	/* 23 */
	_nts_0,	/* 24 */
	_nts_0,	/* 25 */
	_nts_0,	/* 26 */
	_nts_0,	/* 27 */
	_nts_0,	/* 28 */
	_nts_0,	/* 29 */
	_nts_0,	/* 30 */
	_nts_0,	/* 31 */
	_nts_0,	/* 32 */
	_nts_0,	/* 33 */
	_nts_3,	/* 34 */
	_nts_1,	/* 35 */
	_nts_4,	/* 36 */
	_nts_0,	/* 37 */
	_nts_0,	/* 38 */
	_nts_0,	/* 39 */
	_nts_0,	/* 40 */
	_nts_0,	/* 41 */
	_nts_0,	/* 42 */
	_nts_5,	/* 43 */
	_nts_0,	/* 44 */
	_nts_0,	/* 45 */
	_nts_0,	/* 46 */
	_nts_5,	/* 47 */
	_nts_5,	/* 48 */
	_nts_5,	/* 49 */
	_nts_5,	/* 50 */
	_nts_5,	/* 51 */
	_nts_6,	/* 52 */
	_nts_6,	/* 53 */
	_nts_6,	/* 54 */
	_nts_6,	/* 55 */
	_nts_6,	/* 56 */
	_nts_7,	/* 57 */
	_nts_7,	/* 58 */
	_nts_7,	/* 59 */
	_nts_7,	/* 60 */
	_nts_7,	/* 61 */
	_nts_7,	/* 62 */
	_nts_7,	/* 63 */
	_nts_7,	/* 64 */
	_nts_8,	/* 65 */
	_nts_8,	/* 66 */
	_nts_8,	/* 67 */
	_nts_8,	/* 68 */
	_nts_8,	/* 69 */
	_nts_8,	/* 70 */
	_nts_8,	/* 71 */
	_nts_8,	/* 72 */
	_nts_8,	/* 73 */
	_nts_8,	/* 74 */
	_nts_8,	/* 75 */
	_nts_8,	/* 76 */
	_nts_9,	/* 77 */
	_nts_9,	/* 78 */
	_nts_10,	/* 79 */
	_nts_10,	/* 80 */
	_nts_10,	/* 81 */
	_nts_10,	/* 82 */
	_nts_11,	/* 83 */
	_nts_11,	/* 84 */
	_nts_12,	/* 85 */
	_nts_12,	/* 86 */
	_nts_12,	/* 87 */
	_nts_12,	/* 88 */
	_nts_12,	/* 89 */
	_nts_13,	/* 90 */
	_nts_13,	/* 91 */
	_nts_9,	/* 92 */
	_nts_9,	/* 93 */
	_nts_9,	/* 94 */
	_nts_14,	/* 95 */
	_nts_14,	/* 96 */
	_nts_12,	/* 97 */
	_nts_12,	/* 98 */
	_nts_12,	/* 99 */
	_nts_12,	/* 100 */
	_nts_12,	/* 101 */
	_nts_13,	/* 102 */
	_nts_13,	/* 103 */
	_nts_9,	/* 104 */
	_nts_9,	/* 105 */
	_nts_9,	/* 106 */
	_nts_14,	/* 107 */
	_nts_14,	/* 108 */
	_nts_2,	/* 109 */
	_nts_15,	/* 110 */
	_nts_15,	/* 111 */
	_nts_15,	/* 112 */
	_nts_16,	/* 113 */
	_nts_16,	/* 114 */
	_nts_16,	/* 115 */
	_nts_17,	/* 116 */
	_nts_17,	/* 117 */
	_nts_12,	/* 118 */
	_nts_12,	/* 119 */
	_nts_9,	/* 120 */
	_nts_9,	/* 121 */
	_nts_18,	/* 122 */
	_nts_18,	/* 123 */
	_nts_18,	/* 124 */
	_nts_19,	/* 125 */
	_nts_19,	/* 126 */
	_nts_13,	/* 127 */
	_nts_13,	/* 128 */
	_nts_13,	/* 129 */
	_nts_8,	/* 130 */
	_nts_15,	/* 131 */
	_nts_15,	/* 132 */
	_nts_16,	/* 133 */
	_nts_16,	/* 134 */
	_nts_17,	/* 135 */
	_nts_17,	/* 136 */
	_nts_18,	/* 137 */
	_nts_18,	/* 138 */
	_nts_19,	/* 139 */
	_nts_19,	/* 140 */
	_nts_13,	/* 141 */
	_nts_13,	/* 142 */
	_nts_2,	/* 143 */
	_nts_13,	/* 144 */
	_nts_13,	/* 145 */
	_nts_13,	/* 146 */
	_nts_13,	/* 147 */
	_nts_13,	/* 148 */
	_nts_13,	/* 149 */
	_nts_13,	/* 150 */
	_nts_13,	/* 151 */
	_nts_13,	/* 152 */
	_nts_13,	/* 153 */
	_nts_13,	/* 154 */
	_nts_13,	/* 155 */
	_nts_13,	/* 156 */
	_nts_13,	/* 157 */
	_nts_13,	/* 158 */
	_nts_13,	/* 159 */
	_nts_12,	/* 160 */
	_nts_12,	/* 161 */
	_nts_13,	/* 162 */
	_nts_13,	/* 163 */
	_nts_9,	/* 164 */
	_nts_9,	/* 165 */
	_nts_12,	/* 166 */
	_nts_12,	/* 167 */
	_nts_13,	/* 168 */
	_nts_13,	/* 169 */
	_nts_9,	/* 170 */
	_nts_9,	/* 171 */
	_nts_12,	/* 172 */
	_nts_12,	/* 173 */
	_nts_13,	/* 174 */
	_nts_13,	/* 175 */
	_nts_9,	/* 176 */
	_nts_9,	/* 177 */
	_nts_2,	/* 178 */
	_nts_2,	/* 179 */
	_nts_13,	/* 180 */
	_nts_13,	/* 181 */
	_nts_16,	/* 182 */
	_nts_16,	/* 183 */
	_nts_18,	/* 184 */
	_nts_18,	/* 185 */
	_nts_13,	/* 186 */
	_nts_13,	/* 187 */
	_nts_16,	/* 188 */
	_nts_16,	/* 189 */
	_nts_18,	/* 190 */
	_nts_18,	/* 191 */
	_nts_13,	/* 192 */
	_nts_13,	/* 193 */
	_nts_16,	/* 194 */
	_nts_16,	/* 195 */
	_nts_18,	/* 196 */
	_nts_18,	/* 197 */
	_nts_2,	/* 198 */
	_nts_2,	/* 199 */
	_nts_14,	/* 200 */
	_nts_14,	/* 201 */
	_nts_14,	/* 202 */
	_nts_14,	/* 203 */
	_nts_13,	/* 204 */
	_nts_13,	/* 205 */
	_nts_13,	/* 206 */
	_nts_13,	/* 207 */
	_nts_14,	/* 208 */
	_nts_14,	/* 209 */
	_nts_14,	/* 210 */
	_nts_14,	/* 211 */
	_nts_13,	/* 212 */
	_nts_13,	/* 213 */
	_nts_13,	/* 214 */
	_nts_13,	/* 215 */
	_nts_2,	/* 216 */
	_nts_2,	/* 217 */
	_nts_2,	/* 218 */
	_nts_2,	/* 219 */
	_nts_2,	/* 220 */
	_nts_2,	/* 221 */
	_nts_2,	/* 222 */
	_nts_2,	/* 223 */
	_nts_7,	/* 224 */
	_nts_7,	/* 225 */
	_nts_2,	/* 226 */
	_nts_2,	/* 227 */
	_nts_2,	/* 228 */
	_nts_2,	/* 229 */
	_nts_2,	/* 230 */
	_nts_2,	/* 231 */
	_nts_2,	/* 232 */
	_nts_2,	/* 233 */
	_nts_0,	/* 234 */
	_nts_7,	/* 235 */
	_nts_2,	/* 236 */
	_nts_13,	/* 237 */
	_nts_13,	/* 238 */
	_nts_9,	/* 239 */
	_nts_9,	/* 240 */
	_nts_13,	/* 241 */
	_nts_13,	/* 242 */
	_nts_9,	/* 243 */
	_nts_9,	/* 244 */
	_nts_13,	/* 245 */
	_nts_9,	/* 246 */
	_nts_13,	/* 247 */
	_nts_9,	/* 248 */
	_nts_13,	/* 249 */
	_nts_9,	/* 250 */
	_nts_13,	/* 251 */
	_nts_9,	/* 252 */
	_nts_13,	/* 253 */
	_nts_9,	/* 254 */
	_nts_13,	/* 255 */
	_nts_9,	/* 256 */
	_nts_13,	/* 257 */
	_nts_9,	/* 258 */
	_nts_13,	/* 259 */
	_nts_9,	/* 260 */
	_nts_16,	/* 261 */
	_nts_16,	/* 262 */
	_nts_18,	/* 263 */
	_nts_18,	/* 264 */
	_nts_13,	/* 265 */
	_nts_13,	/* 266 */
	_nts_16,	/* 267 */
	_nts_16,	/* 268 */
	_nts_18,	/* 269 */
	_nts_18,	/* 270 */
	_nts_13,	/* 271 */
	_nts_13,	/* 272 */
	_nts_16,	/* 273 */
	_nts_16,	/* 274 */
	_nts_18,	/* 275 */
	_nts_18,	/* 276 */
	_nts_13,	/* 277 */
	_nts_13,	/* 278 */
	_nts_16,	/* 279 */
	_nts_16,	/* 280 */
	_nts_18,	/* 281 */
	_nts_18,	/* 282 */
	_nts_13,	/* 283 */
	_nts_13,	/* 284 */
	_nts_16,	/* 285 */
	_nts_16,	/* 286 */
	_nts_18,	/* 287 */
	_nts_18,	/* 288 */
	_nts_13,	/* 289 */
	_nts_13,	/* 290 */
	_nts_16,	/* 291 */
	_nts_16,	/* 292 */
	_nts_18,	/* 293 */
	_nts_18,	/* 294 */
	_nts_13,	/* 295 */
	_nts_13,	/* 296 */
	_nts_15,	/* 297 */
	_nts_15,	/* 298 */
	_nts_19,	/* 299 */
	_nts_19,	/* 300 */
	_nts_15,	/* 301 */
	_nts_15,	/* 302 */
	_nts_19,	/* 303 */
	_nts_19,	/* 304 */
	_nts_15,	/* 305 */
	_nts_15,	/* 306 */
	_nts_19,	/* 307 */
	_nts_19,	/* 308 */
	_nts_15,	/* 309 */
	_nts_15,	/* 310 */
	_nts_19,	/* 311 */
	_nts_19,	/* 312 */
	_nts_15,	/* 313 */
	_nts_15,	/* 314 */
	_nts_19,	/* 315 */
	_nts_19,	/* 316 */
	_nts_15,	/* 317 */
	_nts_15,	/* 318 */
	_nts_19,	/* 319 */
	_nts_19,	/* 320 */
	_nts_2,	/* 321 */
	_nts_2,	/* 322 */
	_nts_2,	/* 323 */
	_nts_2,	/* 324 */
	_nts_2,	/* 325 */
	_nts_2,	/* 326 */
	_nts_2,	/* 327 */
	_nts_2,	/* 328 */
	_nts_7,	/* 329 */
	_nts_7,	/* 330 */
	_nts_7,	/* 331 */
	_nts_7,	/* 332 */
	_nts_7,	/* 333 */
	_nts_7,	/* 334 */
	_nts_7,	/* 335 */
	_nts_7,	/* 336 */
	_nts_7,	/* 337 */
	_nts_2,	/* 338 */
	_nts_2,	/* 339 */
	_nts_2,	/* 340 */
	_nts_2,	/* 341 */
	_nts_2,	/* 342 */
	_nts_2,	/* 343 */
	_nts_2,	/* 344 */
	_nts_2,	/* 345 */
	_nts_0,	/* 346 */
	_nts_2,	/* 347 */
	_nts_2,	/* 348 */
	_nts_2,	/* 349 */
	_nts_2,	/* 350 */
	_nts_2,	/* 351 */
	_nts_2,	/* 352 */
	_nts_2,	/* 353 */
	_nts_2,	/* 354 */
	_nts_2,	/* 355 */
};

static char *_templates[] = {
/* 0 */	0,
/* 1 */	"# read vreg\n",	/* reg: INDIRI1(VREGP) */
/* 2 */	"# read vreg\n",	/* reg: INDIRU1(VREGP) */
/* 3 */	"# read vreg\n",	/* reg: INDIRI2(VREGP) */
/* 4 */	"# read vreg\n",	/* reg: INDIRU2(VREGP) */
/* 5 */	"# read vreg\n",	/* reg: INDIRP2(VREGP) */
/* 6 */	"# read vreg\n",	/* reg: INDIRI4(VREGP) */
/* 7 */	"# read vreg\n",	/* reg: INDIRU4(VREGP) */
/* 8 */	"# read vreg\n",	/* reg: INDIRP4(VREGP) */
/* 9 */	"# add vreg+vreg\n",	/* reg: ADDI2(INDIRI2(VREGP),INDIRI2(VREGP)) */
/* 10 */	"# add vreg+vreg\n",	/* reg: ADDU2(INDIRU2(VREGP),INDIRU2(VREGP)) */
/* 11 */	"# add vreg+vreg\n",	/* reg: ADDP2(INDIRP2(VREGP),INDIRI2(VREGP)) */
/* 12 */	"# add vreg+const\n",	/* reg: ADDI2(INDIRI2(VREGP),con2) */
/* 13 */	"# add vreg+const\n",	/* reg: ADDU2(INDIRU2(VREGP),con2) */
/* 14 */	"# mul vreg*vreg\n",	/* reg: MULI2(INDIRI2(VREGP),INDIRI2(VREGP)) */
/* 15 */	"# mul vreg*vreg\n",	/* reg: MULU2(INDIRU2(VREGP),INDIRU2(VREGP)) */
/* 16 */	"# write vreg\n",	/* stmt: ASGNI1(VREGP,reg) */
/* 17 */	"# write vreg\n",	/* stmt: ASGNU1(VREGP,reg) */
/* 18 */	"# write vreg\n",	/* stmt: ASGNI2(VREGP,reg) */
/* 19 */	"# write vreg\n",	/* stmt: ASGNU2(VREGP,reg) */
/* 20 */	"# write vreg\n",	/* stmt: ASGNP2(VREGP,reg) */
/* 21 */	"# write vreg\n",	/* stmt: ASGNI4(VREGP,reg) */
/* 22 */	"# write vreg\n",	/* stmt: ASGNU4(VREGP,reg) */
/* 23 */	"# write vreg\n",	/* stmt: ASGNP4(VREGP,reg) */
/* 24 */	"%a",	/* con1: CNSTI1 */
/* 25 */	"%a",	/* con1: CNSTU1 */
/* 26 */	"%a",	/* con2: CNSTI2 */
/* 27 */	"%a",	/* con2: CNSTU2 */
/* 28 */	"%a",	/* con2: CNSTP2 */
/* 29 */	"%a",	/* con4: CNSTI4 */
/* 30 */	"%a",	/* con4: CNSTU4 */
/* 31 */	"%a",	/* con4: CNSTP4 */
/* 32 */	"%a",	/* conN: CNSTI1 */
/* 33 */	"%a",	/* conN: CNSTU1 */
/* 34 */	"    LDI %0\n",	/* reg: con1 */
/* 35 */	"    LDI %0\n",	/* reg: con2 */
/* 36 */	"    LDI lo(%0)\n    PUSH\n    LDI hi(%0)\n",	/* reg: con4 */
/* 37 */	"%a",	/* addr: ADDRGP2 */
/* 38 */	"%a",	/* addr: ADDRGP4 */
/* 39 */	"%a,FP",	/* faddr: ADDRFP2 */
/* 40 */	"%a,FP",	/* faddr: ADDRLP2 */
/* 41 */	"%a,FP",	/* faddr: ADDRFP4 */
/* 42 */	"%a,FP",	/* faddr: ADDRLP4 */
/* 43 */	"%0",	/* addr: faddr */
/* 44 */	"    LDI %a\n",	/* reg: ADDRGP2 */
/* 45 */	"    LDI %a\n",	/* reg: ADDRFP2 */
/* 46 */	"    LDI %a\n",	/* reg: ADDRLP2 */
/* 47 */	"    LDA %0\n",	/* reg: INDIRI1(faddr) */
/* 48 */	"    LDA %0\n",	/* reg: INDIRU1(faddr) */
/* 49 */	"    LDA %0\n",	/* reg: INDIRI2(faddr) */
/* 50 */	"    LDA %0\n",	/* reg: INDIRU2(faddr) */
/* 51 */	"    LDA %0\n",	/* reg: INDIRP2(faddr) */
/* 52 */	"    STA %0\n",	/* stmt: ASGNI1(faddr,reg) */
/* 53 */	"    STA %0\n",	/* stmt: ASGNU1(faddr,reg) */
/* 54 */	"    STA %0\n",	/* stmt: ASGNI2(faddr,reg) */
/* 55 */	"    STA %0\n",	/* stmt: ASGNU2(faddr,reg) */
/* 56 */	"    STA %0\n",	/* stmt: ASGNP2(faddr,reg) */
/* 57 */	"    LDA %0\n",	/* reg: INDIRI1(addr) */
/* 58 */	"    LDA %0\n",	/* reg: INDIRU1(addr) */
/* 59 */	"    LDA %0\n",	/* reg: INDIRI2(addr) */
/* 60 */	"    LDA %0\n",	/* reg: INDIRU2(addr) */
/* 61 */	"    LDA %0\n",	/* reg: INDIRP2(addr) */
/* 62 */	"    LDA %0\n    PUSH\n    LDA %0+2\n",	/* reg: INDIRI4(addr) */
/* 63 */	"    LDA %0\n    PUSH\n    LDA %0+2\n",	/* reg: INDIRU4(addr) */
/* 64 */	"    LDA %0\n    PUSH\n    LDA %0+2\n",	/* reg: INDIRP4(addr) */
/* 65 */	"    STA %0\n",	/* stmt: ASGNI1(addr,reg) */
/* 66 */	"    STA %0\n",	/* stmt: ASGNU1(addr,reg) */
/* 67 */	"    STA %0\n",	/* stmt: ASGNI2(addr,reg) */
/* 68 */	"    STA %0\n",	/* stmt: ASGNU2(addr,reg) */
/* 69 */	"    STA %0\n",	/* stmt: ASGNP2(addr,reg) */
/* 70 */	"    STA %0+2\n    POP\n    STA %0\n",	/* stmt: ASGNI4(addr,reg) */
/* 71 */	"    STA %0+2\n    POP\n    STA %0\n",	/* stmt: ASGNU4(addr,reg) */
/* 72 */	"    STA %0+2\n    POP\n    STA %0\n",	/* stmt: ASGNP4(addr,reg) */
/* 73 */	"    TAX\n    LDA %0,X\n",	/* reg: INDIRI1(ADDI2(addr,reg)) */
/* 74 */	"    TAX\n    LDA %0,X\n",	/* reg: INDIRU1(ADDI2(addr,reg)) */
/* 75 */	"    TAX\n    LDA %0,X\n",	/* reg: INDIRI1(ADDP2(addr,reg)) */
/* 76 */	"    TAX\n    LDA %0,X\n",	/* reg: INDIRU1(ADDP2(addr,reg)) */
/* 77 */	"    TAX\n    LDA %1,X\n",	/* reg: INDIRI1(ADDP2(reg,addr)) */
/* 78 */	"    TAX\n    LDA %1,X\n",	/* reg: INDIRU1(ADDP2(reg,addr)) */
/* 79 */	"    TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n",	/* stmt: ASGNI1(ADDI2(addr,reg),reg) */
/* 80 */	"    TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n",	/* stmt: ASGNU1(ADDI2(addr,reg),reg) */
/* 81 */	"    TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n",	/* stmt: ASGNI1(ADDP2(addr,reg),reg) */
/* 82 */	"    TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n",	/* stmt: ASGNU1(ADDP2(addr,reg),reg) */
/* 83 */	"    TAY\n    POP\n    TAX\n    TYA\n    STA %1,X\n",	/* stmt: ASGNI1(ADDP2(reg,addr),reg) */
/* 84 */	"    TAY\n    POP\n    TAX\n    TYA\n    STA %1,X\n",	/* stmt: ASGNU1(ADDP2(reg,addr),reg) */
/* 85 */	"    LDA %0\n    ADD %1\n",	/* reg: ADDI1(INDIRI1(addr),INDIRI1(addr)) */
/* 86 */	"    LDA %0\n    ADD %1\n",	/* reg: ADDU1(INDIRU1(addr),INDIRU1(addr)) */
/* 87 */	"    LDA %0\n    ADD %1\n",	/* reg: ADDI1(INDIRU1(addr),INDIRU1(addr)) */
/* 88 */	"    LDA %0\n    ADD %1\n",	/* reg: ADDI1(LOADI1(INDIRU1(addr)),LOADI1(INDIRU1(addr))) */
/* 89 */	"    LDA %0\n    ADD %1\n",	/* reg: ADDU1(LOADU1(INDIRU1(addr)),LOADU1(INDIRU1(addr))) */
/* 90 */	"    ADDX\n",	/* reg: ADDI1(reg,reg) */
/* 91 */	"    ADDX\n",	/* reg: ADDU1(reg,reg) */
/* 92 */	"    ADD %1\n",	/* reg: ADDI1(reg,INDIRI1(addr)) */
/* 93 */	"    ADD %1\n",	/* reg: ADDU1(reg,INDIRU1(addr)) */
/* 94 */	"    ADD %1\n",	/* reg: ADDI1(reg,INDIRU1(addr)) */
/* 95 */	"    INC\n",	/* reg: ADDI1(reg,conN) */
/* 96 */	"    INC\n",	/* reg: ADDU1(reg,conN) */
/* 97 */	"    LDA %0\n    SUB %1\n",	/* reg: SUBI1(INDIRI1(addr),INDIRI1(addr)) */
/* 98 */	"    LDA %0\n    SUB %1\n",	/* reg: SUBU1(INDIRU1(addr),INDIRU1(addr)) */
/* 99 */	"    LDA %0\n    SUB %1\n",	/* reg: SUBI1(INDIRU1(addr),INDIRU1(addr)) */
/* 100 */	"    LDA %0\n    SUB %1\n",	/* reg: SUBI1(LOADI1(INDIRU1(addr)),LOADI1(INDIRU1(addr))) */
/* 101 */	"    LDA %0\n    SUB %1\n",	/* reg: SUBU1(LOADU1(INDIRU1(addr)),LOADU1(INDIRU1(addr))) */
/* 102 */	"    SUBX\n",	/* reg: SUBI1(reg,reg) */
/* 103 */	"    SUBX\n",	/* reg: SUBU1(reg,reg) */
/* 104 */	"    SUB %1\n",	/* reg: SUBI1(reg,INDIRI1(addr)) */
/* 105 */	"    SUB %1\n",	/* reg: SUBU1(reg,INDIRU1(addr)) */
/* 106 */	"    SUB %1\n",	/* reg: SUBI1(reg,INDIRU1(addr)) */
/* 107 */	"    DEC\n",	/* reg: SUBI1(reg,conN) */
/* 108 */	"    DEC\n",	/* reg: SUBU1(reg,conN) */
/* 109 */	"    NEG\n",	/* reg: NEGI1(reg) */
/* 110 */	"    LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n",	/* reg: ADDI2(INDIRI2(faddr),con2) */
/* 111 */	"    LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n",	/* reg: ADDU2(INDIRU2(faddr),con2) */
/* 112 */	"    LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n",	/* reg: ADDP2(INDIRP2(faddr),con2) */
/* 113 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n",	/* reg: ADDI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 114 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n",	/* reg: ADDU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 115 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n",	/* reg: ADDP2(INDIRP2(faddr),INDIRI2(faddr)) */
/* 116 */	"    LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n",	/* reg: ADDI2(INDIRI2(addr),con2) */
/* 117 */	"    LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n",	/* reg: ADDU2(INDIRU2(addr),con2) */
/* 118 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n",	/* reg: ADDI2(INDIRI2(addr),INDIRI2(addr)) */
/* 119 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n",	/* reg: ADDU2(INDIRU2(addr),INDIRU2(addr)) */
/* 120 */	"    STA _tmp\n    LDA %1\n    ADD _tmp\n",	/* reg: ADDI2(reg,INDIRI2(addr)) */
/* 121 */	"    STA _tmp\n    LDA %1\n    ADD _tmp\n",	/* reg: ADDU2(reg,INDIRU2(addr)) */
/* 122 */	"    STA _tmp\n    LDA %1\n    ADD _tmp\n",	/* reg: ADDI2(reg,INDIRI2(faddr)) */
/* 123 */	"    STA _tmp\n    LDA %1\n    ADD _tmp\n",	/* reg: ADDU2(reg,INDIRU2(faddr)) */
/* 124 */	"    STA _tmp\n    LDA %1\n    ADD _tmp\n",	/* reg: ADDP2(reg,INDIRP2(faddr)) */
/* 125 */	"    STA _tmp\n    LDI %1\n    ADD _tmp\n",	/* reg: ADDI2(reg,con2) */
/* 126 */	"    STA _tmp\n    LDI %1\n    ADD _tmp\n",	/* reg: ADDU2(reg,con2) */
/* 127 */	"    STA _tmp\n    POP\n    ADD _tmp\n",	/* reg: ADDI2(reg,reg) */
/* 128 */	"    STA _tmp\n    POP\n    ADD _tmp\n",	/* reg: ADDU2(reg,reg) */
/* 129 */	"    STA _tmp\n    POP\n    ADD _tmp\n",	/* reg: ADDP2(reg,reg) */
/* 130 */	"%0",	/* addr: ADDP2(addr,reg) */
/* 131 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n",	/* reg: SUBI2(INDIRI2(faddr),con2) */
/* 132 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n",	/* reg: SUBU2(INDIRU2(faddr),con2) */
/* 133 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n",	/* reg: SUBI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 134 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n",	/* reg: SUBU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 135 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n",	/* reg: SUBI2(INDIRI2(addr),con2) */
/* 136 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n",	/* reg: SUBU2(INDIRU2(addr),con2) */
/* 137 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n",	/* reg: SUBI2(reg,INDIRI2(faddr)) */
/* 138 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n",	/* reg: SUBU2(reg,INDIRU2(faddr)) */
/* 139 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n",	/* reg: SUBI2(reg,con2) */
/* 140 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n",	/* reg: SUBU2(reg,con2) */
/* 141 */	"    STA _tmp\n    POP\n    SUB _tmp\n",	/* reg: SUBI2(reg,reg) */
/* 142 */	"    STA _tmp\n    POP\n    SUB _tmp\n",	/* reg: SUBU2(reg,reg) */
/* 143 */	"    NEG\n",	/* reg: NEGI2(reg) */
/* 144 */	"    STA _tmp\n    POP\n    STA _tmp_hi\n    POP\n    STA _tmp2_hi\n    POP\n    ADD _tmp\n    PUSH\n    LDA _tmp2_hi\n    ADC _tmp_hi\n",	/* reg: ADDI4(reg,reg) */
/* 145 */	"    STA _tmp\n    POP\n    STA _tmp_hi\n    POP\n    STA _tmp2_hi\n    POP\n    ADD _tmp\n    PUSH\n    LDA _tmp2_hi\n    ADC _tmp_hi\n",	/* reg: ADDU4(reg,reg) */
/* 146 */	"    STA _tmp\n    POP\n    STA _tmp_hi\n    POP\n    STA _tmp2_hi\n    POP\n    SUB _tmp\n    PUSH\n    LDA _tmp2_hi\n    SBC _tmp_hi\n",	/* reg: SUBI4(reg,reg) */
/* 147 */	"    STA _tmp\n    POP\n    STA _tmp_hi\n    POP\n    STA _tmp2_hi\n    POP\n    SUB _tmp\n    PUSH\n    LDA _tmp2_hi\n    SBC _tmp_hi\n",	/* reg: SUBU4(reg,reg) */
/* 148 */	"    TAX\n    POP\n    MUL\n",	/* reg: MULI1(reg,reg) */
/* 149 */	"    TAX\n    POP\n    MUL\n",	/* reg: MULU1(reg,reg) */
/* 150 */	"    TAX\n    POP\n    MUL\n",	/* reg: MULI2(reg,reg) */
/* 151 */	"    TAX\n    POP\n    MUL\n",	/* reg: MULU2(reg,reg) */
/* 152 */	"    TAX\n    POP\n    DIV\n",	/* reg: DIVI1(reg,reg) */
/* 153 */	"    TAX\n    POP\n    DIV\n",	/* reg: DIVU1(reg,reg) */
/* 154 */	"    TAX\n    POP\n    DIV\n",	/* reg: DIVI2(reg,reg) */
/* 155 */	"    TAX\n    POP\n    DIV\n",	/* reg: DIVU2(reg,reg) */
/* 156 */	"    TAX\n    POP\n    MOD\n",	/* reg: MODI1(reg,reg) */
/* 157 */	"    TAX\n    POP\n    MOD\n",	/* reg: MODU1(reg,reg) */
/* 158 */	"    TAX\n    POP\n    MOD\n",	/* reg: MODI2(reg,reg) */
/* 159 */	"    TAX\n    POP\n    MOD\n",	/* reg: MODU2(reg,reg) */
/* 160 */	"    LDA %0\n    AND %1\n",	/* reg: BANDI1(INDIRI1(addr),INDIRI1(addr)) */
/* 161 */	"    LDA %0\n    AND %1\n",	/* reg: BANDU1(INDIRU1(addr),INDIRU1(addr)) */
/* 162 */	"    ANDX\n",	/* reg: BANDI1(reg,reg) */
/* 163 */	"    ANDX\n",	/* reg: BANDU1(reg,reg) */
/* 164 */	"    AND %1\n",	/* reg: BANDI1(reg,INDIRI1(addr)) */
/* 165 */	"    AND %1\n",	/* reg: BANDU1(reg,INDIRU1(addr)) */
/* 166 */	"    LDA %0\n    OR %1\n",	/* reg: BORI1(INDIRI1(addr),INDIRI1(addr)) */
/* 167 */	"    LDA %0\n    OR %1\n",	/* reg: BORU1(INDIRU1(addr),INDIRU1(addr)) */
/* 168 */	"    ORX\n",	/* reg: BORI1(reg,reg) */
/* 169 */	"    ORX\n",	/* reg: BORU1(reg,reg) */
/* 170 */	"    OR %1\n",	/* reg: BORI1(reg,INDIRI1(addr)) */
/* 171 */	"    OR %1\n",	/* reg: BORU1(reg,INDIRU1(addr)) */
/* 172 */	"    LDA %0\n    XOR %1\n",	/* reg: BXORI1(INDIRI1(addr),INDIRI1(addr)) */
/* 173 */	"    LDA %0\n    XOR %1\n",	/* reg: BXORU1(INDIRU1(addr),INDIRU1(addr)) */
/* 174 */	"    XORX\n",	/* reg: BXORI1(reg,reg) */
/* 175 */	"    XORX\n",	/* reg: BXORU1(reg,reg) */
/* 176 */	"    XOR %1\n",	/* reg: BXORI1(reg,INDIRI1(addr)) */
/* 177 */	"    XOR %1\n",	/* reg: BXORU1(reg,INDIRU1(addr)) */
/* 178 */	"    NOT\n",	/* reg: BCOMI1(reg) */
/* 179 */	"    NOT\n",	/* reg: BCOMU1(reg) */
/* 180 */	"    STA _tmp\n    POP\n    AND _tmp\n",	/* reg: BANDI2(reg,reg) */
/* 181 */	"    STA _tmp\n    POP\n    AND _tmp\n",	/* reg: BANDU2(reg,reg) */
/* 182 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    AND _tmp\n",	/* reg: BANDI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 183 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    AND _tmp\n",	/* reg: BANDU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 184 */	"    STA _tmp\n    LDA %1\n    AND _tmp\n",	/* reg: BANDI2(reg,INDIRI2(faddr)) */
/* 185 */	"    STA _tmp\n    LDA %1\n    AND _tmp\n",	/* reg: BANDU2(reg,INDIRU2(faddr)) */
/* 186 */	"    STA _tmp\n    POP\n    OR _tmp\n",	/* reg: BORI2(reg,reg) */
/* 187 */	"    STA _tmp\n    POP\n    OR _tmp\n",	/* reg: BORU2(reg,reg) */
/* 188 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    OR _tmp\n",	/* reg: BORI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 189 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    OR _tmp\n",	/* reg: BORU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 190 */	"    STA _tmp\n    LDA %1\n    OR _tmp\n",	/* reg: BORI2(reg,INDIRI2(faddr)) */
/* 191 */	"    STA _tmp\n    LDA %1\n    OR _tmp\n",	/* reg: BORU2(reg,INDIRU2(faddr)) */
/* 192 */	"    STA _tmp\n    POP\n    XOR _tmp\n",	/* reg: BXORI2(reg,reg) */
/* 193 */	"    STA _tmp\n    POP\n    XOR _tmp\n",	/* reg: BXORU2(reg,reg) */
/* 194 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    XOR _tmp\n",	/* reg: BXORI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 195 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    XOR _tmp\n",	/* reg: BXORU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 196 */	"    STA _tmp\n    LDA %1\n    XOR _tmp\n",	/* reg: BXORI2(reg,INDIRI2(faddr)) */
/* 197 */	"    STA _tmp\n    LDA %1\n    XOR _tmp\n",	/* reg: BXORU2(reg,INDIRU2(faddr)) */
/* 198 */	"    NOT\n",	/* reg: BCOMI2(reg) */
/* 199 */	"    NOT\n",	/* reg: BCOMU2(reg) */
/* 200 */	"    SHL\n",	/* reg: LSHI2(reg,conN) */
/* 201 */	"    SHL\n",	/* reg: LSHU2(reg,conN) */
/* 202 */	"    SHR\n",	/* reg: RSHU2(reg,conN) */
/* 203 */	"    ASR\n",	/* reg: RSHI2(reg,conN) */
/* 204 */	"    TAX\n    POP\n    TAY\n_shl2_%a:\n    TXA\n    JZ _shl2d_%a\n    TYA\n    SHL\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shl2_%a\n_shl2d_%a:\n    TYA\n",	/* reg: LSHI2(reg,reg) */
/* 205 */	"    TAX\n    POP\n    TAY\n_shl2_%a:\n    TXA\n    JZ _shl2d_%a\n    TYA\n    SHL\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shl2_%a\n_shl2d_%a:\n    TYA\n",	/* reg: LSHU2(reg,reg) */
/* 206 */	"    TAX\n    POP\n    TAY\n_shr2_%a:\n    TXA\n    JZ _shr2d_%a\n    TYA\n    SHR\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shr2_%a\n_shr2d_%a:\n    TYA\n",	/* reg: RSHU2(reg,reg) */
/* 207 */	"    TAX\n    POP\n    TAY\n_asr2_%a:\n    TXA\n    JZ _asr2d_%a\n    TYA\n    ASR\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _asr2_%a\n_asr2d_%a:\n    TYA\n",	/* reg: RSHI2(reg,reg) */
/* 208 */	"    SHL\n",	/* reg: LSHI1(reg,conN) */
/* 209 */	"    SHL\n",	/* reg: LSHU1(reg,conN) */
/* 210 */	"    SHR\n",	/* reg: RSHU1(reg,conN) */
/* 211 */	"    ASR\n",	/* reg: RSHI1(reg,conN) */
/* 212 */	"    TAX\n    POP\n    TAY\n_shl_%a:\n    TXA\n    JZ _shld_%a\n    TYA\n    SHL\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shl_%a\n_shld_%a:\n    TYA\n",	/* reg: LSHI1(reg,reg) */
/* 213 */	"    TAX\n    POP\n    TAY\n_shl_%a:\n    TXA\n    JZ _shld_%a\n    TYA\n    SHL\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shl_%a\n_shld_%a:\n    TYA\n",	/* reg: LSHU1(reg,reg) */
/* 214 */	"    TAX\n    POP\n    TAY\n_shr_%a:\n    TXA\n    JZ _shrd_%a\n    TYA\n    SHR\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shr_%a\n_shrd_%a:\n    TYA\n",	/* reg: RSHU1(reg,reg) */
/* 215 */	"    TAX\n    POP\n    TAY\n_asr_%a:\n    TXA\n    JZ _asrd_%a\n    TYA\n    ASR\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _asr_%a\n_asrd_%a:\n    TYA\n",	/* reg: RSHI1(reg,reg) */
/* 216 */	"    AND _mask_ff\n",	/* reg: CVII1(reg) */
/* 217 */	"    AND _mask_ff\n",	/* reg: CVIU1(reg) */
/* 218 */	"    AND _mask_ff\n",	/* reg: CVUI1(reg) */
/* 219 */	"    AND _mask_ff\n",	/* reg: CVUU1(reg) */
/* 220 */	"; cvii2 - sign extend 8 to 16\n",	/* reg: CVII2(reg) */
/* 221 */	"; cviu2 - zero extend 8 to 16\n",	/* reg: CVIU2(reg) */
/* 222 */	"; cvui2 - already 16-bit\n",	/* reg: CVUI2(reg) */
/* 223 */	"; cvuu2 - already 16-bit\n",	/* reg: CVUU2(reg) */
/* 224 */	"    LDA %0\n    AND _mask_ff\n",	/* reg: CVII1(INDIRI2(addr)) */
/* 225 */	"    LDA %0\n    AND _mask_ff\n",	/* reg: CVUU1(INDIRU2(addr)) */
/* 226 */	"; cvpu2\n",	/* reg: CVPU2(reg) */
/* 227 */	"; cvup2\n",	/* reg: CVUP2(reg) */
/* 228 */	"    TAY\n    JN _sx4_%a\n    LDI 0\n    JMP _sx4d_%a\n_sx4_%a:\n    LDI 0xFFFF\n_sx4d_%a:\n    PUSH\n    TYA\n",	/* reg: CVII4(reg) */
/* 229 */	"    PUSH\n    LDI 0\n",	/* reg: CVIU4(reg) */
/* 230 */	"    PUSH\n    LDI 0\n",	/* reg: CVUI4(reg) */
/* 231 */	"    PUSH\n    LDI 0\n",	/* reg: CVUU4(reg) */
/* 232 */	"    PUSH\n    LDI 0\n",	/* reg: CVPU4(reg) */
/* 233 */	"; cvup4 - truncate to pointer\n",	/* reg: CVUP4(reg) */
/* 234 */	"%a:\n",	/* stmt: LABELV */
/* 235 */	"    JMP %0\n",	/* stmt: JUMPV(addr) */
/* 236 */	"    JMP %0\n",	/* stmt: JUMPV(reg) */
/* 237 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQI1(reg,reg) */
/* 238 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQU1(reg,reg) */
/* 239 */	"    CMP %1\n    JZ %a\n",	/* stmt: EQI1(reg,INDIRI1(addr)) */
/* 240 */	"    CMP %1\n    JZ %a\n",	/* stmt: EQU1(reg,INDIRU1(addr)) */
/* 241 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEI1(reg,reg) */
/* 242 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEU1(reg,reg) */
/* 243 */	"    CMP %1\n    JNZ %a\n",	/* stmt: NEI1(reg,INDIRI1(addr)) */
/* 244 */	"    CMP %1\n    JNZ %a\n",	/* stmt: NEU1(reg,INDIRU1(addr)) */
/* 245 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JN %a\n",	/* stmt: LTI1(reg,reg) */
/* 246 */	"    CMP %1\n    JN %a\n",	/* stmt: LTI1(reg,INDIRI1(addr)) */
/* 247 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JC %a\n",	/* stmt: LTU1(reg,reg) */
/* 248 */	"    CMP %1\n    JC %a\n",	/* stmt: LTU1(reg,INDIRU1(addr)) */
/* 249 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JLE %a\n",	/* stmt: LEI1(reg,reg) */
/* 250 */	"    CMP %1\n    JLE %a\n",	/* stmt: LEI1(reg,INDIRI1(addr)) */
/* 251 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JBE %a\n",	/* stmt: LEU1(reg,reg) */
/* 252 */	"    CMP %1\n    JBE %a\n",	/* stmt: LEU1(reg,INDIRU1(addr)) */
/* 253 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JGT %a\n",	/* stmt: GTI1(reg,reg) */
/* 254 */	"    CMP %1\n    JGT %a\n",	/* stmt: GTI1(reg,INDIRI1(addr)) */
/* 255 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JA %a\n",	/* stmt: GTU1(reg,reg) */
/* 256 */	"    CMP %1\n    JA %a\n",	/* stmt: GTU1(reg,INDIRU1(addr)) */
/* 257 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JGE %a\n",	/* stmt: GEI1(reg,reg) */
/* 258 */	"    CMP %1\n    JGE %a\n",	/* stmt: GEI1(reg,INDIRI1(addr)) */
/* 259 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JNC %a\n",	/* stmt: GEU1(reg,reg) */
/* 260 */	"    CMP %1\n    JNC %a\n",	/* stmt: GEU1(reg,INDIRU1(addr)) */
/* 261 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 262 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 263 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQI2(reg,INDIRI2(faddr)) */
/* 264 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQU2(reg,INDIRU2(faddr)) */
/* 265 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQI2(reg,reg) */
/* 266 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQU2(reg,reg) */
/* 267 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 268 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 269 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEI2(reg,INDIRI2(faddr)) */
/* 270 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEU2(reg,INDIRU2(faddr)) */
/* 271 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEI2(reg,reg) */
/* 272 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEU2(reg,reg) */
/* 273 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JN %a\n",	/* stmt: LTI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 274 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JC %a\n",	/* stmt: LTU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 275 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JN %a\n",	/* stmt: LTI2(reg,INDIRI2(faddr)) */
/* 276 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JC %a\n",	/* stmt: LTU2(reg,INDIRU2(faddr)) */
/* 277 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JN %a\n",	/* stmt: LTI2(reg,reg) */
/* 278 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JC %a\n",	/* stmt: LTU2(reg,reg) */
/* 279 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JLE %a\n",	/* stmt: LEI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 280 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JBE %a\n",	/* stmt: LEU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 281 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JLE %a\n",	/* stmt: LEI2(reg,INDIRI2(faddr)) */
/* 282 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JBE %a\n",	/* stmt: LEU2(reg,INDIRU2(faddr)) */
/* 283 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JLE %a\n",	/* stmt: LEI2(reg,reg) */
/* 284 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JBE %a\n",	/* stmt: LEU2(reg,reg) */
/* 285 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JGT %a\n",	/* stmt: GTI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 286 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JA %a\n",	/* stmt: GTU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 287 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JGT %a\n",	/* stmt: GTI2(reg,INDIRI2(faddr)) */
/* 288 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JA %a\n",	/* stmt: GTU2(reg,INDIRU2(faddr)) */
/* 289 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JGT %a\n",	/* stmt: GTI2(reg,reg) */
/* 290 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JA %a\n",	/* stmt: GTU2(reg,reg) */
/* 291 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JGE %a\n",	/* stmt: GEI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 292 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNC %a\n",	/* stmt: GEU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 293 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JGE %a\n",	/* stmt: GEI2(reg,INDIRI2(faddr)) */
/* 294 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNC %a\n",	/* stmt: GEU2(reg,INDIRU2(faddr)) */
/* 295 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JGE %a\n",	/* stmt: GEI2(reg,reg) */
/* 296 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JNC %a\n",	/* stmt: GEU2(reg,reg) */
/* 297 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JLE %a\n",	/* stmt: LEI2(INDIRI2(faddr),con2) */
/* 298 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JBE %a\n",	/* stmt: LEU2(INDIRU2(faddr),con2) */
/* 299 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JLE %a\n",	/* stmt: LEI2(reg,con2) */
/* 300 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JBE %a\n",	/* stmt: LEU2(reg,con2) */
/* 301 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JGT %a\n",	/* stmt: GTI2(INDIRI2(faddr),con2) */
/* 302 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JA %a\n",	/* stmt: GTU2(INDIRU2(faddr),con2) */
/* 303 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JGT %a\n",	/* stmt: GTI2(reg,con2) */
/* 304 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JA %a\n",	/* stmt: GTU2(reg,con2) */
/* 305 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JGE %a\n",	/* stmt: GEI2(INDIRI2(faddr),con2) */
/* 306 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNC %a\n",	/* stmt: GEU2(INDIRU2(faddr),con2) */
/* 307 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JGE %a\n",	/* stmt: GEI2(reg,con2) */
/* 308 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNC %a\n",	/* stmt: GEU2(reg,con2) */
/* 309 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JN %a\n",	/* stmt: LTI2(INDIRI2(faddr),con2) */
/* 310 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JC %a\n",	/* stmt: LTU2(INDIRU2(faddr),con2) */
/* 311 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JN %a\n",	/* stmt: LTI2(reg,con2) */
/* 312 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JC %a\n",	/* stmt: LTU2(reg,con2) */
/* 313 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQI2(INDIRI2(faddr),con2) */
/* 314 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQU2(INDIRU2(faddr),con2) */
/* 315 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQI2(reg,con2) */
/* 316 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQU2(reg,con2) */
/* 317 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEI2(INDIRI2(faddr),con2) */
/* 318 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEU2(INDIRU2(faddr),con2) */
/* 319 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEI2(reg,con2) */
/* 320 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEU2(reg,con2) */
/* 321 */	"    PUSH\n",	/* stmt: ARGI1(reg) */
/* 322 */	"    PUSH\n",	/* stmt: ARGU1(reg) */
/* 323 */	"    PUSH\n",	/* stmt: ARGI2(reg) */
/* 324 */	"    PUSH\n",	/* stmt: ARGU2(reg) */
/* 325 */	"    PUSH\n",	/* stmt: ARGP2(reg) */
/* 326 */	"    PUSH\n    POP\n    PUSH\n    PUSH\n",	/* stmt: ARGI4(reg) */
/* 327 */	"    PUSH\n    POP\n    PUSH\n    PUSH\n",	/* stmt: ARGU4(reg) */
/* 328 */	"    PUSH\n    POP\n    PUSH\n    PUSH\n",	/* stmt: ARGP4(reg) */
/* 329 */	"    CALL %0\n",	/* reg: CALLI1(addr) */
/* 330 */	"    CALL %0\n",	/* reg: CALLU1(addr) */
/* 331 */	"    CALL %0\n",	/* reg: CALLI2(addr) */
/* 332 */	"    CALL %0\n",	/* reg: CALLU2(addr) */
/* 333 */	"    CALL %0\n",	/* reg: CALLP2(addr) */
/* 334 */	"    CALL %0\n",	/* reg: CALLI4(addr) */
/* 335 */	"    CALL %0\n",	/* reg: CALLU4(addr) */
/* 336 */	"    CALL %0\n",	/* reg: CALLP4(addr) */
/* 337 */	"    CALL %0\n",	/* stmt: CALLV(addr) */
/* 338 */	"; ret - value in AC\n",	/* stmt: RETI1(reg) */
/* 339 */	"; ret - value in AC\n",	/* stmt: RETU1(reg) */
/* 340 */	"; ret - value in AC\n",	/* stmt: RETI2(reg) */
/* 341 */	"; ret - value in AC\n",	/* stmt: RETU2(reg) */
/* 342 */	"; ret - value in AC\n",	/* stmt: RETP2(reg) */
/* 343 */	"; ret - 32-bit value in stack\n",	/* stmt: RETI4(reg) */
/* 344 */	"; ret - 32-bit value in stack\n",	/* stmt: RETU4(reg) */
/* 345 */	"; ret - 32-bit value in stack\n",	/* stmt: RETP4(reg) */
/* 346 */	"; ret void\n",	/* stmt: RETV */
/* 347 */	"",	/* reg: LOADI1(reg) */
/* 348 */	"",	/* reg: LOADU1(reg) */
/* 349 */	"",	/* reg: LOADI2(reg) */
/* 350 */	"",	/* reg: LOADU2(reg) */
/* 351 */	"",	/* reg: LOADP2(reg) */
/* 352 */	"",	/* reg: LOADI4(reg) */
/* 353 */	"",	/* reg: LOADU4(reg) */
/* 354 */	"",	/* reg: LOADP4(reg) */
/* 355 */	"",	/* stmt: reg */
};

static char _isinstruction[] = {
/* 0 */	0,
/* 1 */	1,	/* # read vreg\n */
/* 2 */	1,	/* # read vreg\n */
/* 3 */	1,	/* # read vreg\n */
/* 4 */	1,	/* # read vreg\n */
/* 5 */	1,	/* # read vreg\n */
/* 6 */	1,	/* # read vreg\n */
/* 7 */	1,	/* # read vreg\n */
/* 8 */	1,	/* # read vreg\n */
/* 9 */	1,	/* # add vreg+vreg\n */
/* 10 */	1,	/* # add vreg+vreg\n */
/* 11 */	1,	/* # add vreg+vreg\n */
/* 12 */	1,	/* # add vreg+const\n */
/* 13 */	1,	/* # add vreg+const\n */
/* 14 */	1,	/* # mul vreg*vreg\n */
/* 15 */	1,	/* # mul vreg*vreg\n */
/* 16 */	1,	/* # write vreg\n */
/* 17 */	1,	/* # write vreg\n */
/* 18 */	1,	/* # write vreg\n */
/* 19 */	1,	/* # write vreg\n */
/* 20 */	1,	/* # write vreg\n */
/* 21 */	1,	/* # write vreg\n */
/* 22 */	1,	/* # write vreg\n */
/* 23 */	1,	/* # write vreg\n */
/* 24 */	0,	/* %a */
/* 25 */	0,	/* %a */
/* 26 */	0,	/* %a */
/* 27 */	0,	/* %a */
/* 28 */	0,	/* %a */
/* 29 */	0,	/* %a */
/* 30 */	0,	/* %a */
/* 31 */	0,	/* %a */
/* 32 */	0,	/* %a */
/* 33 */	0,	/* %a */
/* 34 */	1,	/*     LDI %0\n */
/* 35 */	1,	/*     LDI %0\n */
/* 36 */	1,	/*     LDI lo(%0)\n    PUSH\n    LDI hi(%0)\n */
/* 37 */	0,	/* %a */
/* 38 */	0,	/* %a */
/* 39 */	0,	/* %a,FP */
/* 40 */	0,	/* %a,FP */
/* 41 */	0,	/* %a,FP */
/* 42 */	0,	/* %a,FP */
/* 43 */	0,	/* %0 */
/* 44 */	1,	/*     LDI %a\n */
/* 45 */	1,	/*     LDI %a\n */
/* 46 */	1,	/*     LDI %a\n */
/* 47 */	1,	/*     LDA %0\n */
/* 48 */	1,	/*     LDA %0\n */
/* 49 */	1,	/*     LDA %0\n */
/* 50 */	1,	/*     LDA %0\n */
/* 51 */	1,	/*     LDA %0\n */
/* 52 */	1,	/*     STA %0\n */
/* 53 */	1,	/*     STA %0\n */
/* 54 */	1,	/*     STA %0\n */
/* 55 */	1,	/*     STA %0\n */
/* 56 */	1,	/*     STA %0\n */
/* 57 */	1,	/*     LDA %0\n */
/* 58 */	1,	/*     LDA %0\n */
/* 59 */	1,	/*     LDA %0\n */
/* 60 */	1,	/*     LDA %0\n */
/* 61 */	1,	/*     LDA %0\n */
/* 62 */	1,	/*     LDA %0\n    PUSH\n    LDA %0+2\n */
/* 63 */	1,	/*     LDA %0\n    PUSH\n    LDA %0+2\n */
/* 64 */	1,	/*     LDA %0\n    PUSH\n    LDA %0+2\n */
/* 65 */	1,	/*     STA %0\n */
/* 66 */	1,	/*     STA %0\n */
/* 67 */	1,	/*     STA %0\n */
/* 68 */	1,	/*     STA %0\n */
/* 69 */	1,	/*     STA %0\n */
/* 70 */	1,	/*     STA %0+2\n    POP\n    STA %0\n */
/* 71 */	1,	/*     STA %0+2\n    POP\n    STA %0\n */
/* 72 */	1,	/*     STA %0+2\n    POP\n    STA %0\n */
/* 73 */	1,	/*     TAX\n    LDA %0,X\n */
/* 74 */	1,	/*     TAX\n    LDA %0,X\n */
/* 75 */	1,	/*     TAX\n    LDA %0,X\n */
/* 76 */	1,	/*     TAX\n    LDA %0,X\n */
/* 77 */	1,	/*     TAX\n    LDA %1,X\n */
/* 78 */	1,	/*     TAX\n    LDA %1,X\n */
/* 79 */	1,	/*     TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n */
/* 80 */	1,	/*     TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n */
/* 81 */	1,	/*     TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n */
/* 82 */	1,	/*     TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n */
/* 83 */	1,	/*     TAY\n    POP\n    TAX\n    TYA\n    STA %1,X\n */
/* 84 */	1,	/*     TAY\n    POP\n    TAX\n    TYA\n    STA %1,X\n */
/* 85 */	1,	/*     LDA %0\n    ADD %1\n */
/* 86 */	1,	/*     LDA %0\n    ADD %1\n */
/* 87 */	1,	/*     LDA %0\n    ADD %1\n */
/* 88 */	1,	/*     LDA %0\n    ADD %1\n */
/* 89 */	1,	/*     LDA %0\n    ADD %1\n */
/* 90 */	1,	/*     ADDX\n */
/* 91 */	1,	/*     ADDX\n */
/* 92 */	1,	/*     ADD %1\n */
/* 93 */	1,	/*     ADD %1\n */
/* 94 */	1,	/*     ADD %1\n */
/* 95 */	1,	/*     INC\n */
/* 96 */	1,	/*     INC\n */
/* 97 */	1,	/*     LDA %0\n    SUB %1\n */
/* 98 */	1,	/*     LDA %0\n    SUB %1\n */
/* 99 */	1,	/*     LDA %0\n    SUB %1\n */
/* 100 */	1,	/*     LDA %0\n    SUB %1\n */
/* 101 */	1,	/*     LDA %0\n    SUB %1\n */
/* 102 */	1,	/*     SUBX\n */
/* 103 */	1,	/*     SUBX\n */
/* 104 */	1,	/*     SUB %1\n */
/* 105 */	1,	/*     SUB %1\n */
/* 106 */	1,	/*     SUB %1\n */
/* 107 */	1,	/*     DEC\n */
/* 108 */	1,	/*     DEC\n */
/* 109 */	1,	/*     NEG\n */
/* 110 */	1,	/*     LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n */
/* 111 */	1,	/*     LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n */
/* 112 */	1,	/*     LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n */
/* 113 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n */
/* 114 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n */
/* 115 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n */
/* 116 */	1,	/*     LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n */
/* 117 */	1,	/*     LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n */
/* 118 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n */
/* 119 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n */
/* 120 */	1,	/*     STA _tmp\n    LDA %1\n    ADD _tmp\n */
/* 121 */	1,	/*     STA _tmp\n    LDA %1\n    ADD _tmp\n */
/* 122 */	1,	/*     STA _tmp\n    LDA %1\n    ADD _tmp\n */
/* 123 */	1,	/*     STA _tmp\n    LDA %1\n    ADD _tmp\n */
/* 124 */	1,	/*     STA _tmp\n    LDA %1\n    ADD _tmp\n */
/* 125 */	1,	/*     STA _tmp\n    LDI %1\n    ADD _tmp\n */
/* 126 */	1,	/*     STA _tmp\n    LDI %1\n    ADD _tmp\n */
/* 127 */	1,	/*     STA _tmp\n    POP\n    ADD _tmp\n */
/* 128 */	1,	/*     STA _tmp\n    POP\n    ADD _tmp\n */
/* 129 */	1,	/*     STA _tmp\n    POP\n    ADD _tmp\n */
/* 130 */	0,	/* %0 */
/* 131 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n */
/* 132 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n */
/* 133 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n */
/* 134 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n */
/* 135 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n */
/* 136 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n */
/* 137 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n */
/* 138 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n */
/* 139 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n */
/* 140 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n */
/* 141 */	1,	/*     STA _tmp\n    POP\n    SUB _tmp\n */
/* 142 */	1,	/*     STA _tmp\n    POP\n    SUB _tmp\n */
/* 143 */	1,	/*     NEG\n */
/* 144 */	1,	/*     STA _tmp\n    POP\n    STA _tmp_hi\n    POP\n    STA _tmp2_hi\n    POP\n    ADD _tmp\n    PUSH\n    LDA _tmp2_hi\n    ADC _tmp_hi\n */
/* 145 */	1,	/*     STA _tmp\n    POP\n    STA _tmp_hi\n    POP\n    STA _tmp2_hi\n    POP\n    ADD _tmp\n    PUSH\n    LDA _tmp2_hi\n    ADC _tmp_hi\n */
/* 146 */	1,	/*     STA _tmp\n    POP\n    STA _tmp_hi\n    POP\n    STA _tmp2_hi\n    POP\n    SUB _tmp\n    PUSH\n    LDA _tmp2_hi\n    SBC _tmp_hi\n */
/* 147 */	1,	/*     STA _tmp\n    POP\n    STA _tmp_hi\n    POP\n    STA _tmp2_hi\n    POP\n    SUB _tmp\n    PUSH\n    LDA _tmp2_hi\n    SBC _tmp_hi\n */
/* 148 */	1,	/*     TAX\n    POP\n    MUL\n */
/* 149 */	1,	/*     TAX\n    POP\n    MUL\n */
/* 150 */	1,	/*     TAX\n    POP\n    MUL\n */
/* 151 */	1,	/*     TAX\n    POP\n    MUL\n */
/* 152 */	1,	/*     TAX\n    POP\n    DIV\n */
/* 153 */	1,	/*     TAX\n    POP\n    DIV\n */
/* 154 */	1,	/*     TAX\n    POP\n    DIV\n */
/* 155 */	1,	/*     TAX\n    POP\n    DIV\n */
/* 156 */	1,	/*     TAX\n    POP\n    MOD\n */
/* 157 */	1,	/*     TAX\n    POP\n    MOD\n */
/* 158 */	1,	/*     TAX\n    POP\n    MOD\n */
/* 159 */	1,	/*     TAX\n    POP\n    MOD\n */
/* 160 */	1,	/*     LDA %0\n    AND %1\n */
/* 161 */	1,	/*     LDA %0\n    AND %1\n */
/* 162 */	1,	/*     ANDX\n */
/* 163 */	1,	/*     ANDX\n */
/* 164 */	1,	/*     AND %1\n */
/* 165 */	1,	/*     AND %1\n */
/* 166 */	1,	/*     LDA %0\n    OR %1\n */
/* 167 */	1,	/*     LDA %0\n    OR %1\n */
/* 168 */	1,	/*     ORX\n */
/* 169 */	1,	/*     ORX\n */
/* 170 */	1,	/*     OR %1\n */
/* 171 */	1,	/*     OR %1\n */
/* 172 */	1,	/*     LDA %0\n    XOR %1\n */
/* 173 */	1,	/*     LDA %0\n    XOR %1\n */
/* 174 */	1,	/*     XORX\n */
/* 175 */	1,	/*     XORX\n */
/* 176 */	1,	/*     XOR %1\n */
/* 177 */	1,	/*     XOR %1\n */
/* 178 */	1,	/*     NOT\n */
/* 179 */	1,	/*     NOT\n */
/* 180 */	1,	/*     STA _tmp\n    POP\n    AND _tmp\n */
/* 181 */	1,	/*     STA _tmp\n    POP\n    AND _tmp\n */
/* 182 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    AND _tmp\n */
/* 183 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    AND _tmp\n */
/* 184 */	1,	/*     STA _tmp\n    LDA %1\n    AND _tmp\n */
/* 185 */	1,	/*     STA _tmp\n    LDA %1\n    AND _tmp\n */
/* 186 */	1,	/*     STA _tmp\n    POP\n    OR _tmp\n */
/* 187 */	1,	/*     STA _tmp\n    POP\n    OR _tmp\n */
/* 188 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    OR _tmp\n */
/* 189 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    OR _tmp\n */
/* 190 */	1,	/*     STA _tmp\n    LDA %1\n    OR _tmp\n */
/* 191 */	1,	/*     STA _tmp\n    LDA %1\n    OR _tmp\n */
/* 192 */	1,	/*     STA _tmp\n    POP\n    XOR _tmp\n */
/* 193 */	1,	/*     STA _tmp\n    POP\n    XOR _tmp\n */
/* 194 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    XOR _tmp\n */
/* 195 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    XOR _tmp\n */
/* 196 */	1,	/*     STA _tmp\n    LDA %1\n    XOR _tmp\n */
/* 197 */	1,	/*     STA _tmp\n    LDA %1\n    XOR _tmp\n */
/* 198 */	1,	/*     NOT\n */
/* 199 */	1,	/*     NOT\n */
/* 200 */	1,	/*     SHL\n */
/* 201 */	1,	/*     SHL\n */
/* 202 */	1,	/*     SHR\n */
/* 203 */	1,	/*     ASR\n */
/* 204 */	1,	/*     TAX\n    POP\n    TAY\n_shl2_%a:\n    TXA\n    JZ _shl2d_%a\n    TYA\n    SHL\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shl2_%a\n_shl2d_%a:\n    TYA\n */
/* 205 */	1,	/*     TAX\n    POP\n    TAY\n_shl2_%a:\n    TXA\n    JZ _shl2d_%a\n    TYA\n    SHL\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shl2_%a\n_shl2d_%a:\n    TYA\n */
/* 206 */	1,	/*     TAX\n    POP\n    TAY\n_shr2_%a:\n    TXA\n    JZ _shr2d_%a\n    TYA\n    SHR\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shr2_%a\n_shr2d_%a:\n    TYA\n */
/* 207 */	1,	/*     TAX\n    POP\n    TAY\n_asr2_%a:\n    TXA\n    JZ _asr2d_%a\n    TYA\n    ASR\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _asr2_%a\n_asr2d_%a:\n    TYA\n */
/* 208 */	1,	/*     SHL\n */
/* 209 */	1,	/*     SHL\n */
/* 210 */	1,	/*     SHR\n */
/* 211 */	1,	/*     ASR\n */
/* 212 */	1,	/*     TAX\n    POP\n    TAY\n_shl_%a:\n    TXA\n    JZ _shld_%a\n    TYA\n    SHL\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shl_%a\n_shld_%a:\n    TYA\n */
/* 213 */	1,	/*     TAX\n    POP\n    TAY\n_shl_%a:\n    TXA\n    JZ _shld_%a\n    TYA\n    SHL\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shl_%a\n_shld_%a:\n    TYA\n */
/* 214 */	1,	/*     TAX\n    POP\n    TAY\n_shr_%a:\n    TXA\n    JZ _shrd_%a\n    TYA\n    SHR\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shr_%a\n_shrd_%a:\n    TYA\n */
/* 215 */	1,	/*     TAX\n    POP\n    TAY\n_asr_%a:\n    TXA\n    JZ _asrd_%a\n    TYA\n    ASR\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _asr_%a\n_asrd_%a:\n    TYA\n */
/* 216 */	1,	/*     AND _mask_ff\n */
/* 217 */	1,	/*     AND _mask_ff\n */
/* 218 */	1,	/*     AND _mask_ff\n */
/* 219 */	1,	/*     AND _mask_ff\n */
/* 220 */	1,	/* ; cvii2 - sign extend 8 to 16\n */
/* 221 */	1,	/* ; cviu2 - zero extend 8 to 16\n */
/* 222 */	1,	/* ; cvui2 - already 16-bit\n */
/* 223 */	1,	/* ; cvuu2 - already 16-bit\n */
/* 224 */	1,	/*     LDA %0\n    AND _mask_ff\n */
/* 225 */	1,	/*     LDA %0\n    AND _mask_ff\n */
/* 226 */	1,	/* ; cvpu2\n */
/* 227 */	1,	/* ; cvup2\n */
/* 228 */	1,	/*     TAY\n    JN _sx4_%a\n    LDI 0\n    JMP _sx4d_%a\n_sx4_%a:\n    LDI 0xFFFF\n_sx4d_%a:\n    PUSH\n    TYA\n */
/* 229 */	1,	/*     PUSH\n    LDI 0\n */
/* 230 */	1,	/*     PUSH\n    LDI 0\n */
/* 231 */	1,	/*     PUSH\n    LDI 0\n */
/* 232 */	1,	/*     PUSH\n    LDI 0\n */
/* 233 */	1,	/* ; cvup4 - truncate to pointer\n */
/* 234 */	1,	/* %a:\n */
/* 235 */	1,	/*     JMP %0\n */
/* 236 */	1,	/*     JMP %0\n */
/* 237 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JZ %a\n */
/* 238 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JZ %a\n */
/* 239 */	1,	/*     CMP %1\n    JZ %a\n */
/* 240 */	1,	/*     CMP %1\n    JZ %a\n */
/* 241 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JNZ %a\n */
/* 242 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JNZ %a\n */
/* 243 */	1,	/*     CMP %1\n    JNZ %a\n */
/* 244 */	1,	/*     CMP %1\n    JNZ %a\n */
/* 245 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JN %a\n */
/* 246 */	1,	/*     CMP %1\n    JN %a\n */
/* 247 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JC %a\n */
/* 248 */	1,	/*     CMP %1\n    JC %a\n */
/* 249 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JLE %a\n */
/* 250 */	1,	/*     CMP %1\n    JLE %a\n */
/* 251 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JBE %a\n */
/* 252 */	1,	/*     CMP %1\n    JBE %a\n */
/* 253 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JGT %a\n */
/* 254 */	1,	/*     CMP %1\n    JGT %a\n */
/* 255 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JA %a\n */
/* 256 */	1,	/*     CMP %1\n    JA %a\n */
/* 257 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JGE %a\n */
/* 258 */	1,	/*     CMP %1\n    JGE %a\n */
/* 259 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JNC %a\n */
/* 260 */	1,	/*     CMP %1\n    JNC %a\n */
/* 261 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JZ %a\n */
/* 262 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JZ %a\n */
/* 263 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JZ %a\n */
/* 264 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JZ %a\n */
/* 265 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JZ %a\n */
/* 266 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JZ %a\n */
/* 267 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNZ %a\n */
/* 268 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNZ %a\n */
/* 269 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNZ %a\n */
/* 270 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNZ %a\n */
/* 271 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JNZ %a\n */
/* 272 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JNZ %a\n */
/* 273 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JN %a\n */
/* 274 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JC %a\n */
/* 275 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JN %a\n */
/* 276 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JC %a\n */
/* 277 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JN %a\n */
/* 278 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JC %a\n */
/* 279 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JLE %a\n */
/* 280 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JBE %a\n */
/* 281 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JLE %a\n */
/* 282 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JBE %a\n */
/* 283 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JLE %a\n */
/* 284 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JBE %a\n */
/* 285 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JGT %a\n */
/* 286 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JA %a\n */
/* 287 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JGT %a\n */
/* 288 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JA %a\n */
/* 289 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JGT %a\n */
/* 290 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JA %a\n */
/* 291 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JGE %a\n */
/* 292 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNC %a\n */
/* 293 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JGE %a\n */
/* 294 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNC %a\n */
/* 295 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JGE %a\n */
/* 296 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JNC %a\n */
/* 297 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JLE %a\n */
/* 298 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JBE %a\n */
/* 299 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JLE %a\n */
/* 300 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JBE %a\n */
/* 301 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JGT %a\n */
/* 302 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JA %a\n */
/* 303 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JGT %a\n */
/* 304 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JA %a\n */
/* 305 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JGE %a\n */
/* 306 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNC %a\n */
/* 307 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JGE %a\n */
/* 308 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNC %a\n */
/* 309 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JN %a\n */
/* 310 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JC %a\n */
/* 311 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JN %a\n */
/* 312 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JC %a\n */
/* 313 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JZ %a\n */
/* 314 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JZ %a\n */
/* 315 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JZ %a\n */
/* 316 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JZ %a\n */
/* 317 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNZ %a\n */
/* 318 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNZ %a\n */
/* 319 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNZ %a\n */
/* 320 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNZ %a\n */
/* 321 */	1,	/*     PUSH\n */
/* 322 */	1,	/*     PUSH\n */
/* 323 */	1,	/*     PUSH\n */
/* 324 */	1,	/*     PUSH\n */
/* 325 */	1,	/*     PUSH\n */
/* 326 */	1,	/*     PUSH\n    POP\n    PUSH\n    PUSH\n */
/* 327 */	1,	/*     PUSH\n    POP\n    PUSH\n    PUSH\n */
/* 328 */	1,	/*     PUSH\n    POP\n    PUSH\n    PUSH\n */
/* 329 */	1,	/*     CALL %0\n */
/* 330 */	1,	/*     CALL %0\n */
/* 331 */	1,	/*     CALL %0\n */
/* 332 */	1,	/*     CALL %0\n */
/* 333 */	1,	/*     CALL %0\n */
/* 334 */	1,	/*     CALL %0\n */
/* 335 */	1,	/*     CALL %0\n */
/* 336 */	1,	/*     CALL %0\n */
/* 337 */	1,	/*     CALL %0\n */
/* 338 */	1,	/* ; ret - value in AC\n */
/* 339 */	1,	/* ; ret - value in AC\n */
/* 340 */	1,	/* ; ret - value in AC\n */
/* 341 */	1,	/* ; ret - value in AC\n */
/* 342 */	1,	/* ; ret - value in AC\n */
/* 343 */	1,	/* ; ret - 32-bit value in stack\n */
/* 344 */	1,	/* ; ret - 32-bit value in stack\n */
/* 345 */	1,	/* ; ret - 32-bit value in stack\n */
/* 346 */	1,	/* ; ret void\n */
/* 347 */	0,	/*  */
/* 348 */	0,	/*  */
/* 349 */	0,	/*  */
/* 350 */	0,	/*  */
/* 351 */	0,	/*  */
/* 352 */	0,	/*  */
/* 353 */	0,	/*  */
/* 354 */	0,	/*  */
/* 355 */	0,	/*  */
};

static char *_string[] = {
/* 0 */	0,
/* 1 */	"reg: INDIRI1(VREGP)",
/* 2 */	"reg: INDIRU1(VREGP)",
/* 3 */	"reg: INDIRI2(VREGP)",
/* 4 */	"reg: INDIRU2(VREGP)",
/* 5 */	"reg: INDIRP2(VREGP)",
/* 6 */	"reg: INDIRI4(VREGP)",
/* 7 */	"reg: INDIRU4(VREGP)",
/* 8 */	"reg: INDIRP4(VREGP)",
/* 9 */	"reg: ADDI2(INDIRI2(VREGP),INDIRI2(VREGP))",
/* 10 */	"reg: ADDU2(INDIRU2(VREGP),INDIRU2(VREGP))",
/* 11 */	"reg: ADDP2(INDIRP2(VREGP),INDIRI2(VREGP))",
/* 12 */	"reg: ADDI2(INDIRI2(VREGP),con2)",
/* 13 */	"reg: ADDU2(INDIRU2(VREGP),con2)",
/* 14 */	"reg: MULI2(INDIRI2(VREGP),INDIRI2(VREGP))",
/* 15 */	"reg: MULU2(INDIRU2(VREGP),INDIRU2(VREGP))",
/* 16 */	"stmt: ASGNI1(VREGP,reg)",
/* 17 */	"stmt: ASGNU1(VREGP,reg)",
/* 18 */	"stmt: ASGNI2(VREGP,reg)",
/* 19 */	"stmt: ASGNU2(VREGP,reg)",
/* 20 */	"stmt: ASGNP2(VREGP,reg)",
/* 21 */	"stmt: ASGNI4(VREGP,reg)",
/* 22 */	"stmt: ASGNU4(VREGP,reg)",
/* 23 */	"stmt: ASGNP4(VREGP,reg)",
/* 24 */	"con1: CNSTI1",
/* 25 */	"con1: CNSTU1",
/* 26 */	"con2: CNSTI2",
/* 27 */	"con2: CNSTU2",
/* 28 */	"con2: CNSTP2",
/* 29 */	"con4: CNSTI4",
/* 30 */	"con4: CNSTU4",
/* 31 */	"con4: CNSTP4",
/* 32 */	"conN: CNSTI1",
/* 33 */	"conN: CNSTU1",
/* 34 */	"reg: con1",
/* 35 */	"reg: con2",
/* 36 */	"reg: con4",
/* 37 */	"addr: ADDRGP2",
/* 38 */	"addr: ADDRGP4",
/* 39 */	"faddr: ADDRFP2",
/* 40 */	"faddr: ADDRLP2",
/* 41 */	"faddr: ADDRFP4",
/* 42 */	"faddr: ADDRLP4",
/* 43 */	"addr: faddr",
/* 44 */	"reg: ADDRGP2",
/* 45 */	"reg: ADDRFP2",
/* 46 */	"reg: ADDRLP2",
/* 47 */	"reg: INDIRI1(faddr)",
/* 48 */	"reg: INDIRU1(faddr)",
/* 49 */	"reg: INDIRI2(faddr)",
/* 50 */	"reg: INDIRU2(faddr)",
/* 51 */	"reg: INDIRP2(faddr)",
/* 52 */	"stmt: ASGNI1(faddr,reg)",
/* 53 */	"stmt: ASGNU1(faddr,reg)",
/* 54 */	"stmt: ASGNI2(faddr,reg)",
/* 55 */	"stmt: ASGNU2(faddr,reg)",
/* 56 */	"stmt: ASGNP2(faddr,reg)",
/* 57 */	"reg: INDIRI1(addr)",
/* 58 */	"reg: INDIRU1(addr)",
/* 59 */	"reg: INDIRI2(addr)",
/* 60 */	"reg: INDIRU2(addr)",
/* 61 */	"reg: INDIRP2(addr)",
/* 62 */	"reg: INDIRI4(addr)",
/* 63 */	"reg: INDIRU4(addr)",
/* 64 */	"reg: INDIRP4(addr)",
/* 65 */	"stmt: ASGNI1(addr,reg)",
/* 66 */	"stmt: ASGNU1(addr,reg)",
/* 67 */	"stmt: ASGNI2(addr,reg)",
/* 68 */	"stmt: ASGNU2(addr,reg)",
/* 69 */	"stmt: ASGNP2(addr,reg)",
/* 70 */	"stmt: ASGNI4(addr,reg)",
/* 71 */	"stmt: ASGNU4(addr,reg)",
/* 72 */	"stmt: ASGNP4(addr,reg)",
/* 73 */	"reg: INDIRI1(ADDI2(addr,reg))",
/* 74 */	"reg: INDIRU1(ADDI2(addr,reg))",
/* 75 */	"reg: INDIRI1(ADDP2(addr,reg))",
/* 76 */	"reg: INDIRU1(ADDP2(addr,reg))",
/* 77 */	"reg: INDIRI1(ADDP2(reg,addr))",
/* 78 */	"reg: INDIRU1(ADDP2(reg,addr))",
/* 79 */	"stmt: ASGNI1(ADDI2(addr,reg),reg)",
/* 80 */	"stmt: ASGNU1(ADDI2(addr,reg),reg)",
/* 81 */	"stmt: ASGNI1(ADDP2(addr,reg),reg)",
/* 82 */	"stmt: ASGNU1(ADDP2(addr,reg),reg)",
/* 83 */	"stmt: ASGNI1(ADDP2(reg,addr),reg)",
/* 84 */	"stmt: ASGNU1(ADDP2(reg,addr),reg)",
/* 85 */	"reg: ADDI1(INDIRI1(addr),INDIRI1(addr))",
/* 86 */	"reg: ADDU1(INDIRU1(addr),INDIRU1(addr))",
/* 87 */	"reg: ADDI1(INDIRU1(addr),INDIRU1(addr))",
/* 88 */	"reg: ADDI1(LOADI1(INDIRU1(addr)),LOADI1(INDIRU1(addr)))",
/* 89 */	"reg: ADDU1(LOADU1(INDIRU1(addr)),LOADU1(INDIRU1(addr)))",
/* 90 */	"reg: ADDI1(reg,reg)",
/* 91 */	"reg: ADDU1(reg,reg)",
/* 92 */	"reg: ADDI1(reg,INDIRI1(addr))",
/* 93 */	"reg: ADDU1(reg,INDIRU1(addr))",
/* 94 */	"reg: ADDI1(reg,INDIRU1(addr))",
/* 95 */	"reg: ADDI1(reg,conN)",
/* 96 */	"reg: ADDU1(reg,conN)",
/* 97 */	"reg: SUBI1(INDIRI1(addr),INDIRI1(addr))",
/* 98 */	"reg: SUBU1(INDIRU1(addr),INDIRU1(addr))",
/* 99 */	"reg: SUBI1(INDIRU1(addr),INDIRU1(addr))",
/* 100 */	"reg: SUBI1(LOADI1(INDIRU1(addr)),LOADI1(INDIRU1(addr)))",
/* 101 */	"reg: SUBU1(LOADU1(INDIRU1(addr)),LOADU1(INDIRU1(addr)))",
/* 102 */	"reg: SUBI1(reg,reg)",
/* 103 */	"reg: SUBU1(reg,reg)",
/* 104 */	"reg: SUBI1(reg,INDIRI1(addr))",
/* 105 */	"reg: SUBU1(reg,INDIRU1(addr))",
/* 106 */	"reg: SUBI1(reg,INDIRU1(addr))",
/* 107 */	"reg: SUBI1(reg,conN)",
/* 108 */	"reg: SUBU1(reg,conN)",
/* 109 */	"reg: NEGI1(reg)",
/* 110 */	"reg: ADDI2(INDIRI2(faddr),con2)",
/* 111 */	"reg: ADDU2(INDIRU2(faddr),con2)",
/* 112 */	"reg: ADDP2(INDIRP2(faddr),con2)",
/* 113 */	"reg: ADDI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 114 */	"reg: ADDU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 115 */	"reg: ADDP2(INDIRP2(faddr),INDIRI2(faddr))",
/* 116 */	"reg: ADDI2(INDIRI2(addr),con2)",
/* 117 */	"reg: ADDU2(INDIRU2(addr),con2)",
/* 118 */	"reg: ADDI2(INDIRI2(addr),INDIRI2(addr))",
/* 119 */	"reg: ADDU2(INDIRU2(addr),INDIRU2(addr))",
/* 120 */	"reg: ADDI2(reg,INDIRI2(addr))",
/* 121 */	"reg: ADDU2(reg,INDIRU2(addr))",
/* 122 */	"reg: ADDI2(reg,INDIRI2(faddr))",
/* 123 */	"reg: ADDU2(reg,INDIRU2(faddr))",
/* 124 */	"reg: ADDP2(reg,INDIRP2(faddr))",
/* 125 */	"reg: ADDI2(reg,con2)",
/* 126 */	"reg: ADDU2(reg,con2)",
/* 127 */	"reg: ADDI2(reg,reg)",
/* 128 */	"reg: ADDU2(reg,reg)",
/* 129 */	"reg: ADDP2(reg,reg)",
/* 130 */	"addr: ADDP2(addr,reg)",
/* 131 */	"reg: SUBI2(INDIRI2(faddr),con2)",
/* 132 */	"reg: SUBU2(INDIRU2(faddr),con2)",
/* 133 */	"reg: SUBI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 134 */	"reg: SUBU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 135 */	"reg: SUBI2(INDIRI2(addr),con2)",
/* 136 */	"reg: SUBU2(INDIRU2(addr),con2)",
/* 137 */	"reg: SUBI2(reg,INDIRI2(faddr))",
/* 138 */	"reg: SUBU2(reg,INDIRU2(faddr))",
/* 139 */	"reg: SUBI2(reg,con2)",
/* 140 */	"reg: SUBU2(reg,con2)",
/* 141 */	"reg: SUBI2(reg,reg)",
/* 142 */	"reg: SUBU2(reg,reg)",
/* 143 */	"reg: NEGI2(reg)",
/* 144 */	"reg: ADDI4(reg,reg)",
/* 145 */	"reg: ADDU4(reg,reg)",
/* 146 */	"reg: SUBI4(reg,reg)",
/* 147 */	"reg: SUBU4(reg,reg)",
/* 148 */	"reg: MULI1(reg,reg)",
/* 149 */	"reg: MULU1(reg,reg)",
/* 150 */	"reg: MULI2(reg,reg)",
/* 151 */	"reg: MULU2(reg,reg)",
/* 152 */	"reg: DIVI1(reg,reg)",
/* 153 */	"reg: DIVU1(reg,reg)",
/* 154 */	"reg: DIVI2(reg,reg)",
/* 155 */	"reg: DIVU2(reg,reg)",
/* 156 */	"reg: MODI1(reg,reg)",
/* 157 */	"reg: MODU1(reg,reg)",
/* 158 */	"reg: MODI2(reg,reg)",
/* 159 */	"reg: MODU2(reg,reg)",
/* 160 */	"reg: BANDI1(INDIRI1(addr),INDIRI1(addr))",
/* 161 */	"reg: BANDU1(INDIRU1(addr),INDIRU1(addr))",
/* 162 */	"reg: BANDI1(reg,reg)",
/* 163 */	"reg: BANDU1(reg,reg)",
/* 164 */	"reg: BANDI1(reg,INDIRI1(addr))",
/* 165 */	"reg: BANDU1(reg,INDIRU1(addr))",
/* 166 */	"reg: BORI1(INDIRI1(addr),INDIRI1(addr))",
/* 167 */	"reg: BORU1(INDIRU1(addr),INDIRU1(addr))",
/* 168 */	"reg: BORI1(reg,reg)",
/* 169 */	"reg: BORU1(reg,reg)",
/* 170 */	"reg: BORI1(reg,INDIRI1(addr))",
/* 171 */	"reg: BORU1(reg,INDIRU1(addr))",
/* 172 */	"reg: BXORI1(INDIRI1(addr),INDIRI1(addr))",
/* 173 */	"reg: BXORU1(INDIRU1(addr),INDIRU1(addr))",
/* 174 */	"reg: BXORI1(reg,reg)",
/* 175 */	"reg: BXORU1(reg,reg)",
/* 176 */	"reg: BXORI1(reg,INDIRI1(addr))",
/* 177 */	"reg: BXORU1(reg,INDIRU1(addr))",
/* 178 */	"reg: BCOMI1(reg)",
/* 179 */	"reg: BCOMU1(reg)",
/* 180 */	"reg: BANDI2(reg,reg)",
/* 181 */	"reg: BANDU2(reg,reg)",
/* 182 */	"reg: BANDI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 183 */	"reg: BANDU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 184 */	"reg: BANDI2(reg,INDIRI2(faddr))",
/* 185 */	"reg: BANDU2(reg,INDIRU2(faddr))",
/* 186 */	"reg: BORI2(reg,reg)",
/* 187 */	"reg: BORU2(reg,reg)",
/* 188 */	"reg: BORI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 189 */	"reg: BORU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 190 */	"reg: BORI2(reg,INDIRI2(faddr))",
/* 191 */	"reg: BORU2(reg,INDIRU2(faddr))",
/* 192 */	"reg: BXORI2(reg,reg)",
/* 193 */	"reg: BXORU2(reg,reg)",
/* 194 */	"reg: BXORI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 195 */	"reg: BXORU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 196 */	"reg: BXORI2(reg,INDIRI2(faddr))",
/* 197 */	"reg: BXORU2(reg,INDIRU2(faddr))",
/* 198 */	"reg: BCOMI2(reg)",
/* 199 */	"reg: BCOMU2(reg)",
/* 200 */	"reg: LSHI2(reg,conN)",
/* 201 */	"reg: LSHU2(reg,conN)",
/* 202 */	"reg: RSHU2(reg,conN)",
/* 203 */	"reg: RSHI2(reg,conN)",
/* 204 */	"reg: LSHI2(reg,reg)",
/* 205 */	"reg: LSHU2(reg,reg)",
/* 206 */	"reg: RSHU2(reg,reg)",
/* 207 */	"reg: RSHI2(reg,reg)",
/* 208 */	"reg: LSHI1(reg,conN)",
/* 209 */	"reg: LSHU1(reg,conN)",
/* 210 */	"reg: RSHU1(reg,conN)",
/* 211 */	"reg: RSHI1(reg,conN)",
/* 212 */	"reg: LSHI1(reg,reg)",
/* 213 */	"reg: LSHU1(reg,reg)",
/* 214 */	"reg: RSHU1(reg,reg)",
/* 215 */	"reg: RSHI1(reg,reg)",
/* 216 */	"reg: CVII1(reg)",
/* 217 */	"reg: CVIU1(reg)",
/* 218 */	"reg: CVUI1(reg)",
/* 219 */	"reg: CVUU1(reg)",
/* 220 */	"reg: CVII2(reg)",
/* 221 */	"reg: CVIU2(reg)",
/* 222 */	"reg: CVUI2(reg)",
/* 223 */	"reg: CVUU2(reg)",
/* 224 */	"reg: CVII1(INDIRI2(addr))",
/* 225 */	"reg: CVUU1(INDIRU2(addr))",
/* 226 */	"reg: CVPU2(reg)",
/* 227 */	"reg: CVUP2(reg)",
/* 228 */	"reg: CVII4(reg)",
/* 229 */	"reg: CVIU4(reg)",
/* 230 */	"reg: CVUI4(reg)",
/* 231 */	"reg: CVUU4(reg)",
/* 232 */	"reg: CVPU4(reg)",
/* 233 */	"reg: CVUP4(reg)",
/* 234 */	"stmt: LABELV",
/* 235 */	"stmt: JUMPV(addr)",
/* 236 */	"stmt: JUMPV(reg)",
/* 237 */	"stmt: EQI1(reg,reg)",
/* 238 */	"stmt: EQU1(reg,reg)",
/* 239 */	"stmt: EQI1(reg,INDIRI1(addr))",
/* 240 */	"stmt: EQU1(reg,INDIRU1(addr))",
/* 241 */	"stmt: NEI1(reg,reg)",
/* 242 */	"stmt: NEU1(reg,reg)",
/* 243 */	"stmt: NEI1(reg,INDIRI1(addr))",
/* 244 */	"stmt: NEU1(reg,INDIRU1(addr))",
/* 245 */	"stmt: LTI1(reg,reg)",
/* 246 */	"stmt: LTI1(reg,INDIRI1(addr))",
/* 247 */	"stmt: LTU1(reg,reg)",
/* 248 */	"stmt: LTU1(reg,INDIRU1(addr))",
/* 249 */	"stmt: LEI1(reg,reg)",
/* 250 */	"stmt: LEI1(reg,INDIRI1(addr))",
/* 251 */	"stmt: LEU1(reg,reg)",
/* 252 */	"stmt: LEU1(reg,INDIRU1(addr))",
/* 253 */	"stmt: GTI1(reg,reg)",
/* 254 */	"stmt: GTI1(reg,INDIRI1(addr))",
/* 255 */	"stmt: GTU1(reg,reg)",
/* 256 */	"stmt: GTU1(reg,INDIRU1(addr))",
/* 257 */	"stmt: GEI1(reg,reg)",
/* 258 */	"stmt: GEI1(reg,INDIRI1(addr))",
/* 259 */	"stmt: GEU1(reg,reg)",
/* 260 */	"stmt: GEU1(reg,INDIRU1(addr))",
/* 261 */	"stmt: EQI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 262 */	"stmt: EQU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 263 */	"stmt: EQI2(reg,INDIRI2(faddr))",
/* 264 */	"stmt: EQU2(reg,INDIRU2(faddr))",
/* 265 */	"stmt: EQI2(reg,reg)",
/* 266 */	"stmt: EQU2(reg,reg)",
/* 267 */	"stmt: NEI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 268 */	"stmt: NEU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 269 */	"stmt: NEI2(reg,INDIRI2(faddr))",
/* 270 */	"stmt: NEU2(reg,INDIRU2(faddr))",
/* 271 */	"stmt: NEI2(reg,reg)",
/* 272 */	"stmt: NEU2(reg,reg)",
/* 273 */	"stmt: LTI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 274 */	"stmt: LTU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 275 */	"stmt: LTI2(reg,INDIRI2(faddr))",
/* 276 */	"stmt: LTU2(reg,INDIRU2(faddr))",
/* 277 */	"stmt: LTI2(reg,reg)",
/* 278 */	"stmt: LTU2(reg,reg)",
/* 279 */	"stmt: LEI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 280 */	"stmt: LEU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 281 */	"stmt: LEI2(reg,INDIRI2(faddr))",
/* 282 */	"stmt: LEU2(reg,INDIRU2(faddr))",
/* 283 */	"stmt: LEI2(reg,reg)",
/* 284 */	"stmt: LEU2(reg,reg)",
/* 285 */	"stmt: GTI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 286 */	"stmt: GTU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 287 */	"stmt: GTI2(reg,INDIRI2(faddr))",
/* 288 */	"stmt: GTU2(reg,INDIRU2(faddr))",
/* 289 */	"stmt: GTI2(reg,reg)",
/* 290 */	"stmt: GTU2(reg,reg)",
/* 291 */	"stmt: GEI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 292 */	"stmt: GEU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 293 */	"stmt: GEI2(reg,INDIRI2(faddr))",
/* 294 */	"stmt: GEU2(reg,INDIRU2(faddr))",
/* 295 */	"stmt: GEI2(reg,reg)",
/* 296 */	"stmt: GEU2(reg,reg)",
/* 297 */	"stmt: LEI2(INDIRI2(faddr),con2)",
/* 298 */	"stmt: LEU2(INDIRU2(faddr),con2)",
/* 299 */	"stmt: LEI2(reg,con2)",
/* 300 */	"stmt: LEU2(reg,con2)",
/* 301 */	"stmt: GTI2(INDIRI2(faddr),con2)",
/* 302 */	"stmt: GTU2(INDIRU2(faddr),con2)",
/* 303 */	"stmt: GTI2(reg,con2)",
/* 304 */	"stmt: GTU2(reg,con2)",
/* 305 */	"stmt: GEI2(INDIRI2(faddr),con2)",
/* 306 */	"stmt: GEU2(INDIRU2(faddr),con2)",
/* 307 */	"stmt: GEI2(reg,con2)",
/* 308 */	"stmt: GEU2(reg,con2)",
/* 309 */	"stmt: LTI2(INDIRI2(faddr),con2)",
/* 310 */	"stmt: LTU2(INDIRU2(faddr),con2)",
/* 311 */	"stmt: LTI2(reg,con2)",
/* 312 */	"stmt: LTU2(reg,con2)",
/* 313 */	"stmt: EQI2(INDIRI2(faddr),con2)",
/* 314 */	"stmt: EQU2(INDIRU2(faddr),con2)",
/* 315 */	"stmt: EQI2(reg,con2)",
/* 316 */	"stmt: EQU2(reg,con2)",
/* 317 */	"stmt: NEI2(INDIRI2(faddr),con2)",
/* 318 */	"stmt: NEU2(INDIRU2(faddr),con2)",
/* 319 */	"stmt: NEI2(reg,con2)",
/* 320 */	"stmt: NEU2(reg,con2)",
/* 321 */	"stmt: ARGI1(reg)",
/* 322 */	"stmt: ARGU1(reg)",
/* 323 */	"stmt: ARGI2(reg)",
/* 324 */	"stmt: ARGU2(reg)",
/* 325 */	"stmt: ARGP2(reg)",
/* 326 */	"stmt: ARGI4(reg)",
/* 327 */	"stmt: ARGU4(reg)",
/* 328 */	"stmt: ARGP4(reg)",
/* 329 */	"reg: CALLI1(addr)",
/* 330 */	"reg: CALLU1(addr)",
/* 331 */	"reg: CALLI2(addr)",
/* 332 */	"reg: CALLU2(addr)",
/* 333 */	"reg: CALLP2(addr)",
/* 334 */	"reg: CALLI4(addr)",
/* 335 */	"reg: CALLU4(addr)",
/* 336 */	"reg: CALLP4(addr)",
/* 337 */	"stmt: CALLV(addr)",
/* 338 */	"stmt: RETI1(reg)",
/* 339 */	"stmt: RETU1(reg)",
/* 340 */	"stmt: RETI2(reg)",
/* 341 */	"stmt: RETU2(reg)",
/* 342 */	"stmt: RETP2(reg)",
/* 343 */	"stmt: RETI4(reg)",
/* 344 */	"stmt: RETU4(reg)",
/* 345 */	"stmt: RETP4(reg)",
/* 346 */	"stmt: RETV",
/* 347 */	"reg: LOADI1(reg)",
/* 348 */	"reg: LOADU1(reg)",
/* 349 */	"reg: LOADI2(reg)",
/* 350 */	"reg: LOADU2(reg)",
/* 351 */	"reg: LOADP2(reg)",
/* 352 */	"reg: LOADI4(reg)",
/* 353 */	"reg: LOADU4(reg)",
/* 354 */	"reg: LOADP4(reg)",
/* 355 */	"stmt: reg",
};

static short _decode_stmt[] = {
	0,
	16,
	17,
	18,
	19,
	20,
	21,
	22,
	23,
	52,
	53,
	54,
	55,
	56,
	65,
	66,
	67,
	68,
	69,
	70,
	71,
	72,
	79,
	80,
	81,
	82,
	83,
	84,
	234,
	235,
	236,
	237,
	238,
	239,
	240,
	241,
	242,
	243,
	244,
	245,
	246,
	247,
	248,
	249,
	250,
	251,
	252,
	253,
	254,
	255,
	256,
	257,
	258,
	259,
	260,
	261,
	262,
	263,
	264,
	265,
	266,
	267,
	268,
	269,
	270,
	271,
	272,
	273,
	274,
	275,
	276,
	277,
	278,
	279,
	280,
	281,
	282,
	283,
	284,
	285,
	286,
	287,
	288,
	289,
	290,
	291,
	292,
	293,
	294,
	295,
	296,
	297,
	298,
	299,
	300,
	301,
	302,
	303,
	304,
	305,
	306,
	307,
	308,
	309,
	310,
	311,
	312,
	313,
	314,
	315,
	316,
	317,
	318,
	319,
	320,
	321,
	322,
	323,
	324,
	325,
	326,
	327,
	328,
	337,
	338,
	339,
	340,
	341,
	342,
	343,
	344,
	345,
	346,
	355,
};

static short _decode_reg[] = {
	0,
	1,
	2,
	3,
	4,
	5,
	6,
	7,
	8,
	9,
	10,
	11,
	12,
	13,
	14,
	15,
	34,
	35,
	36,
	44,
	45,
	46,
	47,
	48,
	49,
	50,
	51,
	57,
	58,
	59,
	60,
	61,
	62,
	63,
	64,
	73,
	74,
	75,
	76,
	77,
	78,
	85,
	86,
	87,
	88,
	89,
	90,
	91,
	92,
	93,
	94,
	95,
	96,
	97,
	98,
	99,
	100,
	101,
	102,
	103,
	104,
	105,
	106,
	107,
	108,
	109,
	110,
	111,
	112,
	113,
	114,
	115,
	116,
	117,
	118,
	119,
	120,
	121,
	122,
	123,
	124,
	125,
	126,
	127,
	128,
	129,
	131,
	132,
	133,
	134,
	135,
	136,
	137,
	138,
	139,
	140,
	141,
	142,
	143,
	144,
	145,
	146,
	147,
	148,
	149,
	150,
	151,
	152,
	153,
	154,
	155,
	156,
	157,
	158,
	159,
	160,
	161,
	162,
	163,
	164,
	165,
	166,
	167,
	168,
	169,
	170,
	171,
	172,
	173,
	174,
	175,
	176,
	177,
	178,
	179,
	180,
	181,
	182,
	183,
	184,
	185,
	186,
	187,
	188,
	189,
	190,
	191,
	192,
	193,
	194,
	195,
	196,
	197,
	198,
	199,
	200,
	201,
	202,
	203,
	204,
	205,
	206,
	207,
	208,
	209,
	210,
	211,
	212,
	213,
	214,
	215,
	216,
	217,
	218,
	219,
	220,
	221,
	222,
	223,
	224,
	225,
	226,
	227,
	228,
	229,
	230,
	231,
	232,
	233,
	329,
	330,
	331,
	332,
	333,
	334,
	335,
	336,
	347,
	348,
	349,
	350,
	351,
	352,
	353,
	354,
};

static short _decode_con2[] = {
	0,
	26,
	27,
	28,
};

static short _decode_con1[] = {
	0,
	24,
	25,
};

static short _decode_con4[] = {
	0,
	29,
	30,
	31,
};

static short _decode_conN[] = {
	0,
	32,
	33,
};

static short _decode_addr[] = {
	0,
	37,
	38,
	43,
	130,
};

static short _decode_faddr[] = {
	0,
	39,
	40,
	41,
	42,
};

static int _rule(void *state, int goalnt) {
	if (goalnt < 1 || goalnt > 8)
		fatal("_rule", "Bad goal nonterminal %d\n", goalnt);
	if (!state)
		return 0;
	switch (goalnt) {
	case _stmt_NT:	return _decode_stmt[((struct _state *)state)->rule._stmt];
	case _reg_NT:	return _decode_reg[((struct _state *)state)->rule._reg];
	case _con2_NT:	return _decode_con2[((struct _state *)state)->rule._con2];
	case _con1_NT:	return _decode_con1[((struct _state *)state)->rule._con1];
	case _con4_NT:	return _decode_con4[((struct _state *)state)->rule._con4];
	case _conN_NT:	return _decode_conN[((struct _state *)state)->rule._conN];
	case _addr_NT:	return _decode_addr[((struct _state *)state)->rule._addr];
	case _faddr_NT:	return _decode_faddr[((struct _state *)state)->rule._faddr];
	default:
		fatal("_rule", "Bad goal nonterminal %d\n", goalnt);
		return 0;
	}
}

static void _closure_reg(NODEPTR_TYPE, int);
static void _closure_con2(NODEPTR_TYPE, int);
static void _closure_con1(NODEPTR_TYPE, int);
static void _closure_con4(NODEPTR_TYPE, int);
static void _closure_faddr(NODEPTR_TYPE, int);

static void _closure_reg(NODEPTR_TYPE a, int c) {
	struct _state *p = STATE_LABEL(a);
	if (c + 0 < p->cost[_stmt_NT]) {
		p->cost[_stmt_NT] = c + 0;
		p->rule._stmt = 133;
	}
}

static void _closure_con2(NODEPTR_TYPE a, int c) {
	struct _state *p = STATE_LABEL(a);
	if (c + 1 < p->cost[_reg_NT]) {
		p->cost[_reg_NT] = c + 1;
		p->rule._reg = 17;
		_closure_reg(a, c + 1);
	}
}

static void _closure_con1(NODEPTR_TYPE a, int c) {
	struct _state *p = STATE_LABEL(a);
	if (c + 1 < p->cost[_reg_NT]) {
		p->cost[_reg_NT] = c + 1;
		p->rule._reg = 16;
		_closure_reg(a, c + 1);
	}
}

static void _closure_con4(NODEPTR_TYPE a, int c) {
	struct _state *p = STATE_LABEL(a);
	if (c + 3 < p->cost[_reg_NT]) {
		p->cost[_reg_NT] = c + 3;
		p->rule._reg = 18;
		_closure_reg(a, c + 3);
	}
}

static void _closure_faddr(NODEPTR_TYPE a, int c) {
	struct _state *p = STATE_LABEL(a);
	if (c + 0 < p->cost[_addr_NT]) {
		p->cost[_addr_NT] = c + 0;
		p->rule._addr = 3;
	}
}

static void _label(NODEPTR_TYPE a) {
	int c;
	struct _state *p;

	if (!a)
		fatal("_label", "Null tree\n", 0);
	STATE_LABEL(a) = p = allocate(sizeof *p, FUNC);
	p->rule._stmt = 0;
	p->cost[1] =
	p->cost[2] =
	p->cost[3] =
	p->cost[4] =
	p->cost[5] =
	p->cost[6] =
	p->cost[7] =
	p->cost[8] =
		0x7fff;
	switch (OP_LABEL(a)) {
	case 41: /* ARGB */
		break;
	case 57: /* ASGNB */
		break;
	case 73: /* INDIRB */
		break;
	case 216: /* CALLV */
		_label(LEFT_CHILD(a));
		/* stmt: CALLV(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 5;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 123;
		}
		break;
	case 217: /* CALLB */
		break;
	case 248: /* RETV */
		/* stmt: RETV */
		if (0 + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = 0 + 0;
			p->rule._stmt = 132;
		}
		break;
	case 584: /* JUMPV */
		_label(LEFT_CHILD(a));
		/* stmt: JUMPV(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 1;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 29;
		}
		/* stmt: JUMPV(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 30;
		}
		break;
	case 600: /* LABELV */
		/* stmt: LABELV */
		if (0 + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = 0 + 0;
			p->rule._stmt = 28;
		}
		break;
	case 711: /* VREGP */
		break;
	case 1045: /* CNSTI1 */
		/* con1: CNSTI1 */
		if (0 + 0 < p->cost[_con1_NT]) {
			p->cost[_con1_NT] = 0 + 0;
			p->rule._con1 = 1;
			_closure_con1(a, 0 + 0);
		}
		/* conN: CNSTI1 */
		c = (range(a, 1, 1));
		if (c + 0 < p->cost[_conN_NT]) {
			p->cost[_conN_NT] = c + 0;
			p->rule._conN = 1;
		}
		break;
	case 1046: /* CNSTU1 */
		/* con1: CNSTU1 */
		if (0 + 0 < p->cost[_con1_NT]) {
			p->cost[_con1_NT] = 0 + 0;
			p->rule._con1 = 2;
			_closure_con1(a, 0 + 0);
		}
		/* conN: CNSTU1 */
		c = (range(a, 1, 1));
		if (c + 0 < p->cost[_conN_NT]) {
			p->cost[_conN_NT] = c + 0;
			p->rule._conN = 2;
		}
		break;
	case 1061: /* ARGI1 */
		_label(LEFT_CHILD(a));
		/* stmt: ARGI1(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 115;
		}
		break;
	case 1062: /* ARGU1 */
		_label(LEFT_CHILD(a));
		/* stmt: ARGU1(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 116;
		}
		break;
	case 1077: /* ASGNI1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* stmt: ASGNI1(VREGP,reg) */
			LEFT_CHILD(a)->op == 711 /* VREGP */
		) {
			c = ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 1;
			}
		}
		/* stmt: ASGNI1(faddr,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 9;
		}
		/* stmt: ASGNI1(addr,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 2;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 14;
		}
		if (	/* stmt: ASGNI1(ADDI2(addr,reg),reg) */
			LEFT_CHILD(a)->op == 2357 /* ADDI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(LEFT_CHILD(a))->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 5;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 22;
			}
		}
		if (	/* stmt: ASGNI1(ADDP2(addr,reg),reg) */
			LEFT_CHILD(a)->op == 2359 /* ADDP2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(LEFT_CHILD(a))->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 5;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 24;
			}
		}
		if (	/* stmt: ASGNI1(ADDP2(reg,addr),reg) */
			LEFT_CHILD(a)->op == 2359 /* ADDP2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 5;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 26;
			}
		}
		break;
	case 1078: /* ASGNU1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* stmt: ASGNU1(VREGP,reg) */
			LEFT_CHILD(a)->op == 711 /* VREGP */
		) {
			c = ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 2;
			}
		}
		/* stmt: ASGNU1(faddr,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 10;
		}
		/* stmt: ASGNU1(addr,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 2;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 15;
		}
		if (	/* stmt: ASGNU1(ADDI2(addr,reg),reg) */
			LEFT_CHILD(a)->op == 2357 /* ADDI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(LEFT_CHILD(a))->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 5;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 23;
			}
		}
		if (	/* stmt: ASGNU1(ADDP2(addr,reg),reg) */
			LEFT_CHILD(a)->op == 2359 /* ADDP2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(LEFT_CHILD(a))->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 5;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 25;
			}
		}
		if (	/* stmt: ASGNU1(ADDP2(reg,addr),reg) */
			LEFT_CHILD(a)->op == 2359 /* ADDP2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 5;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 27;
			}
		}
		break;
	case 1093: /* INDIRI1 */
		_label(LEFT_CHILD(a));
		if (	/* reg: INDIRI1(VREGP) */
			LEFT_CHILD(a)->op == 711 /* VREGP */
		) {
			if (mayrecalc(a)) {
				struct _state *q = a->syms[RX]->u.t.cse->x.state;
				if (q->cost[_stmt_NT] == 0) {
					p->cost[_stmt_NT] = 0;
					p->rule._stmt = q->rule._stmt;
				}
				if (q->cost[_reg_NT] == 0) {
					p->cost[_reg_NT] = 0;
					p->rule._reg = q->rule._reg;
				}
				if (q->cost[_con2_NT] == 0) {
					p->cost[_con2_NT] = 0;
					p->rule._con2 = q->rule._con2;
				}
				if (q->cost[_con1_NT] == 0) {
					p->cost[_con1_NT] = 0;
					p->rule._con1 = q->rule._con1;
				}
				if (q->cost[_con4_NT] == 0) {
					p->cost[_con4_NT] = 0;
					p->rule._con4 = q->rule._con4;
				}
				if (q->cost[_conN_NT] == 0) {
					p->cost[_conN_NT] = 0;
					p->rule._conN = q->rule._conN;
				}
				if (q->cost[_addr_NT] == 0) {
					p->cost[_addr_NT] = 0;
					p->rule._addr = q->rule._addr;
				}
				if (q->cost[_faddr_NT] == 0) {
					p->cost[_faddr_NT] = 0;
					p->rule._faddr = q->rule._faddr;
				}
			}
			c = 0;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 1;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: INDIRI1(faddr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_faddr_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 22;
			_closure_reg(a, c + 0);
		}
		/* reg: INDIRI1(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 2;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 27;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: INDIRI1(ADDI2(addr,reg)) */
			LEFT_CHILD(a)->op == 2357 /* ADDI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(LEFT_CHILD(a))->x.state))->cost[_reg_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 35;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: INDIRI1(ADDP2(addr,reg)) */
			LEFT_CHILD(a)->op == 2359 /* ADDP2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(LEFT_CHILD(a))->x.state))->cost[_reg_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 37;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: INDIRI1(ADDP2(reg,addr)) */
			LEFT_CHILD(a)->op == 2359 /* ADDP2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 39;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 1094: /* INDIRU1 */
		_label(LEFT_CHILD(a));
		if (	/* reg: INDIRU1(VREGP) */
			LEFT_CHILD(a)->op == 711 /* VREGP */
		) {
			if (mayrecalc(a)) {
				struct _state *q = a->syms[RX]->u.t.cse->x.state;
				if (q->cost[_stmt_NT] == 0) {
					p->cost[_stmt_NT] = 0;
					p->rule._stmt = q->rule._stmt;
				}
				if (q->cost[_reg_NT] == 0) {
					p->cost[_reg_NT] = 0;
					p->rule._reg = q->rule._reg;
				}
				if (q->cost[_con2_NT] == 0) {
					p->cost[_con2_NT] = 0;
					p->rule._con2 = q->rule._con2;
				}
				if (q->cost[_con1_NT] == 0) {
					p->cost[_con1_NT] = 0;
					p->rule._con1 = q->rule._con1;
				}
				if (q->cost[_con4_NT] == 0) {
					p->cost[_con4_NT] = 0;
					p->rule._con4 = q->rule._con4;
				}
				if (q->cost[_conN_NT] == 0) {
					p->cost[_conN_NT] = 0;
					p->rule._conN = q->rule._conN;
				}
				if (q->cost[_addr_NT] == 0) {
					p->cost[_addr_NT] = 0;
					p->rule._addr = q->rule._addr;
				}
				if (q->cost[_faddr_NT] == 0) {
					p->cost[_faddr_NT] = 0;
					p->rule._faddr = q->rule._faddr;
				}
			}
			c = 0;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 2;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: INDIRU1(faddr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_faddr_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 23;
			_closure_reg(a, c + 0);
		}
		/* reg: INDIRU1(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 2;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 28;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: INDIRU1(ADDI2(addr,reg)) */
			LEFT_CHILD(a)->op == 2357 /* ADDI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(LEFT_CHILD(a))->x.state))->cost[_reg_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 36;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: INDIRU1(ADDP2(addr,reg)) */
			LEFT_CHILD(a)->op == 2359 /* ADDP2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(LEFT_CHILD(a))->x.state))->cost[_reg_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 38;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: INDIRU1(ADDP2(reg,addr)) */
			LEFT_CHILD(a)->op == 2359 /* ADDP2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 40;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 1157: /* CVII1 */
		_label(LEFT_CHILD(a));
		/* reg: CVII1(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 171;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: CVII1(INDIRI2(addr)) */
			LEFT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 179;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 1158: /* CVIU1 */
		_label(LEFT_CHILD(a));
		/* reg: CVIU1(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 172;
			_closure_reg(a, c + 0);
		}
		break;
	case 1205: /* CVUI1 */
		_label(LEFT_CHILD(a));
		/* reg: CVUI1(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 173;
			_closure_reg(a, c + 0);
		}
		break;
	case 1206: /* CVUU1 */
		_label(LEFT_CHILD(a));
		/* reg: CVUU1(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 174;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: CVUU1(INDIRU2(addr)) */
			LEFT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 180;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 1221: /* NEGI1 */
		_label(LEFT_CHILD(a));
		/* reg: NEGI1(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 65;
			_closure_reg(a, c + 0);
		}
		break;
	case 1237: /* CALLI1 */
		_label(LEFT_CHILD(a));
		/* reg: CALLI1(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 5;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 189;
			_closure_reg(a, c + 0);
		}
		break;
	case 1238: /* CALLU1 */
		_label(LEFT_CHILD(a));
		/* reg: CALLU1(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 5;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 190;
			_closure_reg(a, c + 0);
		}
		break;
	case 1253: /* LOADI1 */
		_label(LEFT_CHILD(a));
		/* reg: LOADI1(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + (move(a));
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 197;
			_closure_reg(a, c + 0);
		}
		break;
	case 1254: /* LOADU1 */
		_label(LEFT_CHILD(a));
		/* reg: LOADU1(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + (move(a));
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 198;
			_closure_reg(a, c + 0);
		}
		break;
	case 1269: /* RETI1 */
		_label(LEFT_CHILD(a));
		/* stmt: RETI1(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 124;
		}
		break;
	case 1270: /* RETU1 */
		_label(LEFT_CHILD(a));
		/* stmt: RETU1(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 125;
		}
		break;
	case 1333: /* ADDI1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: ADDI1(INDIRI1(addr),INDIRI1(addr)) */
			LEFT_CHILD(a)->op == 1093 && /* INDIRI1 */
			RIGHT_CHILD(a)->op == 1093 /* INDIRI1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 41;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDI1(INDIRU1(addr),INDIRU1(addr)) */
			LEFT_CHILD(a)->op == 1094 && /* INDIRU1 */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 43;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDI1(LOADI1(INDIRU1(addr)),LOADI1(INDIRU1(addr))) */
			LEFT_CHILD(a)->op == 1253 && /* LOADI1 */
			LEFT_CHILD(LEFT_CHILD(a))->op == 1094 && /* INDIRU1 */
			RIGHT_CHILD(a)->op == 1253 && /* LOADI1 */
			LEFT_CHILD(RIGHT_CHILD(a))->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(LEFT_CHILD(a)))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(LEFT_CHILD(RIGHT_CHILD(a)))->x.state))->cost[_addr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 44;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: ADDI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 46;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: ADDI1(reg,INDIRI1(addr)) */
			RIGHT_CHILD(a)->op == 1093 /* INDIRI1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 48;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDI1(reg,INDIRU1(addr)) */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 50;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: ADDI1(reg,conN) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_conN_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 51;
			_closure_reg(a, c + 0);
		}
		break;
	case 1334: /* ADDU1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: ADDU1(INDIRU1(addr),INDIRU1(addr)) */
			LEFT_CHILD(a)->op == 1094 && /* INDIRU1 */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 42;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDU1(LOADU1(INDIRU1(addr)),LOADU1(INDIRU1(addr))) */
			LEFT_CHILD(a)->op == 1254 && /* LOADU1 */
			LEFT_CHILD(LEFT_CHILD(a))->op == 1094 && /* INDIRU1 */
			RIGHT_CHILD(a)->op == 1254 && /* LOADU1 */
			LEFT_CHILD(RIGHT_CHILD(a))->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(LEFT_CHILD(a)))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(LEFT_CHILD(RIGHT_CHILD(a)))->x.state))->cost[_addr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 45;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: ADDU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 47;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: ADDU1(reg,INDIRU1(addr)) */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 49;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: ADDU1(reg,conN) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_conN_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 52;
			_closure_reg(a, c + 0);
		}
		break;
	case 1349: /* SUBI1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: SUBI1(INDIRI1(addr),INDIRI1(addr)) */
			LEFT_CHILD(a)->op == 1093 && /* INDIRI1 */
			RIGHT_CHILD(a)->op == 1093 /* INDIRI1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 53;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: SUBI1(INDIRU1(addr),INDIRU1(addr)) */
			LEFT_CHILD(a)->op == 1094 && /* INDIRU1 */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 55;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: SUBI1(LOADI1(INDIRU1(addr)),LOADI1(INDIRU1(addr))) */
			LEFT_CHILD(a)->op == 1253 && /* LOADI1 */
			LEFT_CHILD(LEFT_CHILD(a))->op == 1094 && /* INDIRU1 */
			RIGHT_CHILD(a)->op == 1253 && /* LOADI1 */
			LEFT_CHILD(RIGHT_CHILD(a))->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(LEFT_CHILD(a)))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(LEFT_CHILD(RIGHT_CHILD(a)))->x.state))->cost[_addr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 56;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: SUBI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 58;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: SUBI1(reg,INDIRI1(addr)) */
			RIGHT_CHILD(a)->op == 1093 /* INDIRI1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 60;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: SUBI1(reg,INDIRU1(addr)) */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 62;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: SUBI1(reg,conN) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_conN_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 63;
			_closure_reg(a, c + 0);
		}
		break;
	case 1350: /* SUBU1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: SUBU1(INDIRU1(addr),INDIRU1(addr)) */
			LEFT_CHILD(a)->op == 1094 && /* INDIRU1 */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 54;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: SUBU1(LOADU1(INDIRU1(addr)),LOADU1(INDIRU1(addr))) */
			LEFT_CHILD(a)->op == 1254 && /* LOADU1 */
			LEFT_CHILD(LEFT_CHILD(a))->op == 1094 && /* INDIRU1 */
			RIGHT_CHILD(a)->op == 1254 && /* LOADU1 */
			LEFT_CHILD(RIGHT_CHILD(a))->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(LEFT_CHILD(a)))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(LEFT_CHILD(RIGHT_CHILD(a)))->x.state))->cost[_addr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 57;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: SUBU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 59;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: SUBU1(reg,INDIRU1(addr)) */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 61;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: SUBU1(reg,conN) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_conN_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 64;
			_closure_reg(a, c + 0);
		}
		break;
	case 1365: /* LSHI1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: LSHI1(reg,conN) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_conN_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 163;
			_closure_reg(a, c + 0);
		}
		/* reg: LSHI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 15;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 167;
			_closure_reg(a, c + 0);
		}
		break;
	case 1366: /* LSHU1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: LSHU1(reg,conN) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_conN_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 164;
			_closure_reg(a, c + 0);
		}
		/* reg: LSHU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 15;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 168;
			_closure_reg(a, c + 0);
		}
		break;
	case 1381: /* MODI1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: MODI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 111;
			_closure_reg(a, c + 0);
		}
		break;
	case 1382: /* MODU1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: MODU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 112;
			_closure_reg(a, c + 0);
		}
		break;
	case 1397: /* RSHI1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: RSHI1(reg,conN) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_conN_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 166;
			_closure_reg(a, c + 0);
		}
		/* reg: RSHI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 15;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 170;
			_closure_reg(a, c + 0);
		}
		break;
	case 1398: /* RSHU1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: RSHU1(reg,conN) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_conN_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 165;
			_closure_reg(a, c + 0);
		}
		/* reg: RSHU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 15;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 169;
			_closure_reg(a, c + 0);
		}
		break;
	case 1413: /* BANDI1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: BANDI1(INDIRI1(addr),INDIRI1(addr)) */
			LEFT_CHILD(a)->op == 1093 && /* INDIRI1 */
			RIGHT_CHILD(a)->op == 1093 /* INDIRI1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 115;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BANDI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 117;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BANDI1(reg,INDIRI1(addr)) */
			RIGHT_CHILD(a)->op == 1093 /* INDIRI1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 119;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 1414: /* BANDU1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: BANDU1(INDIRU1(addr),INDIRU1(addr)) */
			LEFT_CHILD(a)->op == 1094 && /* INDIRU1 */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 116;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BANDU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 118;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BANDU1(reg,INDIRU1(addr)) */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 120;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 1429: /* BCOMI1 */
		_label(LEFT_CHILD(a));
		/* reg: BCOMI1(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 133;
			_closure_reg(a, c + 0);
		}
		break;
	case 1430: /* BCOMU1 */
		_label(LEFT_CHILD(a));
		/* reg: BCOMU1(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 134;
			_closure_reg(a, c + 0);
		}
		break;
	case 1445: /* BORI1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: BORI1(INDIRI1(addr),INDIRI1(addr)) */
			LEFT_CHILD(a)->op == 1093 && /* INDIRI1 */
			RIGHT_CHILD(a)->op == 1093 /* INDIRI1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 121;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BORI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 123;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BORI1(reg,INDIRI1(addr)) */
			RIGHT_CHILD(a)->op == 1093 /* INDIRI1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 125;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 1446: /* BORU1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: BORU1(INDIRU1(addr),INDIRU1(addr)) */
			LEFT_CHILD(a)->op == 1094 && /* INDIRU1 */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 122;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BORU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 124;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BORU1(reg,INDIRU1(addr)) */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 126;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 1461: /* BXORI1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: BXORI1(INDIRI1(addr),INDIRI1(addr)) */
			LEFT_CHILD(a)->op == 1093 && /* INDIRI1 */
			RIGHT_CHILD(a)->op == 1093 /* INDIRI1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 127;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BXORI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 129;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BXORI1(reg,INDIRI1(addr)) */
			RIGHT_CHILD(a)->op == 1093 /* INDIRI1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 131;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 1462: /* BXORU1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: BXORU1(INDIRU1(addr),INDIRU1(addr)) */
			LEFT_CHILD(a)->op == 1094 && /* INDIRU1 */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 128;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BXORU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 130;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BXORU1(reg,INDIRU1(addr)) */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 132;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 1477: /* DIVI1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: DIVI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 107;
			_closure_reg(a, c + 0);
		}
		break;
	case 1478: /* DIVU1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: DIVU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 108;
			_closure_reg(a, c + 0);
		}
		break;
	case 1493: /* MULI1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: MULI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 103;
			_closure_reg(a, c + 0);
		}
		break;
	case 1494: /* MULU1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: MULU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 104;
			_closure_reg(a, c + 0);
		}
		break;
	case 1509: /* EQI1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* stmt: EQI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 5;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 31;
		}
		if (	/* stmt: EQI1(reg,INDIRI1(addr)) */
			RIGHT_CHILD(a)->op == 1093 /* INDIRI1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 33;
			}
		}
		break;
	case 1510: /* EQU1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* stmt: EQU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 5;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 32;
		}
		if (	/* stmt: EQU1(reg,INDIRU1(addr)) */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 34;
			}
		}
		break;
	case 1525: /* GEI1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* stmt: GEI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 5;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 51;
		}
		if (	/* stmt: GEI1(reg,INDIRI1(addr)) */
			RIGHT_CHILD(a)->op == 1093 /* INDIRI1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 52;
			}
		}
		break;
	case 1526: /* GEU1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* stmt: GEU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 5;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 53;
		}
		if (	/* stmt: GEU1(reg,INDIRU1(addr)) */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 54;
			}
		}
		break;
	case 1541: /* GTI1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* stmt: GTI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 5;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 47;
		}
		if (	/* stmt: GTI1(reg,INDIRI1(addr)) */
			RIGHT_CHILD(a)->op == 1093 /* INDIRI1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 48;
			}
		}
		break;
	case 1542: /* GTU1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* stmt: GTU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 5;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 49;
		}
		if (	/* stmt: GTU1(reg,INDIRU1(addr)) */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 50;
			}
		}
		break;
	case 1557: /* LEI1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* stmt: LEI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 5;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 43;
		}
		if (	/* stmt: LEI1(reg,INDIRI1(addr)) */
			RIGHT_CHILD(a)->op == 1093 /* INDIRI1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 44;
			}
		}
		break;
	case 1558: /* LEU1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* stmt: LEU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 5;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 45;
		}
		if (	/* stmt: LEU1(reg,INDIRU1(addr)) */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 46;
			}
		}
		break;
	case 1573: /* LTI1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* stmt: LTI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 5;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 39;
		}
		if (	/* stmt: LTI1(reg,INDIRI1(addr)) */
			RIGHT_CHILD(a)->op == 1093 /* INDIRI1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 40;
			}
		}
		break;
	case 1574: /* LTU1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* stmt: LTU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 5;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 41;
		}
		if (	/* stmt: LTU1(reg,INDIRU1(addr)) */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 42;
			}
		}
		break;
	case 1589: /* NEI1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* stmt: NEI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 5;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 35;
		}
		if (	/* stmt: NEI1(reg,INDIRI1(addr)) */
			RIGHT_CHILD(a)->op == 1093 /* INDIRI1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 37;
			}
		}
		break;
	case 1590: /* NEU1 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* stmt: NEU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 5;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 36;
		}
		if (	/* stmt: NEU1(reg,INDIRU1(addr)) */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 38;
			}
		}
		break;
	case 2069: /* CNSTI2 */
		/* con2: CNSTI2 */
		if (0 + 0 < p->cost[_con2_NT]) {
			p->cost[_con2_NT] = 0 + 0;
			p->rule._con2 = 1;
			_closure_con2(a, 0 + 0);
		}
		break;
	case 2070: /* CNSTU2 */
		/* con2: CNSTU2 */
		if (0 + 0 < p->cost[_con2_NT]) {
			p->cost[_con2_NT] = 0 + 0;
			p->rule._con2 = 2;
			_closure_con2(a, 0 + 0);
		}
		break;
	case 2071: /* CNSTP2 */
		/* con2: CNSTP2 */
		if (0 + 0 < p->cost[_con2_NT]) {
			p->cost[_con2_NT] = 0 + 0;
			p->rule._con2 = 3;
			_closure_con2(a, 0 + 0);
		}
		break;
	case 2085: /* ARGI2 */
		_label(LEFT_CHILD(a));
		/* stmt: ARGI2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 117;
		}
		break;
	case 2086: /* ARGU2 */
		_label(LEFT_CHILD(a));
		/* stmt: ARGU2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 118;
		}
		break;
	case 2087: /* ARGP2 */
		_label(LEFT_CHILD(a));
		/* stmt: ARGP2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 119;
		}
		break;
	case 2101: /* ASGNI2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* stmt: ASGNI2(VREGP,reg) */
			LEFT_CHILD(a)->op == 711 /* VREGP */
		) {
			c = ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 3;
			}
		}
		/* stmt: ASGNI2(faddr,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 11;
		}
		/* stmt: ASGNI2(addr,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 2;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 16;
		}
		break;
	case 2102: /* ASGNU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* stmt: ASGNU2(VREGP,reg) */
			LEFT_CHILD(a)->op == 711 /* VREGP */
		) {
			c = ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 4;
			}
		}
		/* stmt: ASGNU2(faddr,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 12;
		}
		/* stmt: ASGNU2(addr,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 2;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 17;
		}
		break;
	case 2103: /* ASGNP2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* stmt: ASGNP2(VREGP,reg) */
			LEFT_CHILD(a)->op == 711 /* VREGP */
		) {
			c = ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 5;
			}
		}
		/* stmt: ASGNP2(faddr,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 13;
		}
		/* stmt: ASGNP2(addr,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 2;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 18;
		}
		break;
	case 2117: /* INDIRI2 */
		_label(LEFT_CHILD(a));
		if (	/* reg: INDIRI2(VREGP) */
			LEFT_CHILD(a)->op == 711 /* VREGP */
		) {
			if (mayrecalc(a)) {
				struct _state *q = a->syms[RX]->u.t.cse->x.state;
				if (q->cost[_stmt_NT] == 0) {
					p->cost[_stmt_NT] = 0;
					p->rule._stmt = q->rule._stmt;
				}
				if (q->cost[_reg_NT] == 0) {
					p->cost[_reg_NT] = 0;
					p->rule._reg = q->rule._reg;
				}
				if (q->cost[_con2_NT] == 0) {
					p->cost[_con2_NT] = 0;
					p->rule._con2 = q->rule._con2;
				}
				if (q->cost[_con1_NT] == 0) {
					p->cost[_con1_NT] = 0;
					p->rule._con1 = q->rule._con1;
				}
				if (q->cost[_con4_NT] == 0) {
					p->cost[_con4_NT] = 0;
					p->rule._con4 = q->rule._con4;
				}
				if (q->cost[_conN_NT] == 0) {
					p->cost[_conN_NT] = 0;
					p->rule._conN = q->rule._conN;
				}
				if (q->cost[_addr_NT] == 0) {
					p->cost[_addr_NT] = 0;
					p->rule._addr = q->rule._addr;
				}
				if (q->cost[_faddr_NT] == 0) {
					p->cost[_faddr_NT] = 0;
					p->rule._faddr = q->rule._faddr;
				}
			}
			c = 0;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 3;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: INDIRI2(faddr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_faddr_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 24;
			_closure_reg(a, c + 0);
		}
		/* reg: INDIRI2(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 2;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 29;
			_closure_reg(a, c + 0);
		}
		break;
	case 2118: /* INDIRU2 */
		_label(LEFT_CHILD(a));
		if (	/* reg: INDIRU2(VREGP) */
			LEFT_CHILD(a)->op == 711 /* VREGP */
		) {
			if (mayrecalc(a)) {
				struct _state *q = a->syms[RX]->u.t.cse->x.state;
				if (q->cost[_stmt_NT] == 0) {
					p->cost[_stmt_NT] = 0;
					p->rule._stmt = q->rule._stmt;
				}
				if (q->cost[_reg_NT] == 0) {
					p->cost[_reg_NT] = 0;
					p->rule._reg = q->rule._reg;
				}
				if (q->cost[_con2_NT] == 0) {
					p->cost[_con2_NT] = 0;
					p->rule._con2 = q->rule._con2;
				}
				if (q->cost[_con1_NT] == 0) {
					p->cost[_con1_NT] = 0;
					p->rule._con1 = q->rule._con1;
				}
				if (q->cost[_con4_NT] == 0) {
					p->cost[_con4_NT] = 0;
					p->rule._con4 = q->rule._con4;
				}
				if (q->cost[_conN_NT] == 0) {
					p->cost[_conN_NT] = 0;
					p->rule._conN = q->rule._conN;
				}
				if (q->cost[_addr_NT] == 0) {
					p->cost[_addr_NT] = 0;
					p->rule._addr = q->rule._addr;
				}
				if (q->cost[_faddr_NT] == 0) {
					p->cost[_faddr_NT] = 0;
					p->rule._faddr = q->rule._faddr;
				}
			}
			c = 0;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 4;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: INDIRU2(faddr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_faddr_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 25;
			_closure_reg(a, c + 0);
		}
		/* reg: INDIRU2(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 2;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 30;
			_closure_reg(a, c + 0);
		}
		break;
	case 2119: /* INDIRP2 */
		_label(LEFT_CHILD(a));
		if (	/* reg: INDIRP2(VREGP) */
			LEFT_CHILD(a)->op == 711 /* VREGP */
		) {
			if (mayrecalc(a)) {
				struct _state *q = a->syms[RX]->u.t.cse->x.state;
				if (q->cost[_stmt_NT] == 0) {
					p->cost[_stmt_NT] = 0;
					p->rule._stmt = q->rule._stmt;
				}
				if (q->cost[_reg_NT] == 0) {
					p->cost[_reg_NT] = 0;
					p->rule._reg = q->rule._reg;
				}
				if (q->cost[_con2_NT] == 0) {
					p->cost[_con2_NT] = 0;
					p->rule._con2 = q->rule._con2;
				}
				if (q->cost[_con1_NT] == 0) {
					p->cost[_con1_NT] = 0;
					p->rule._con1 = q->rule._con1;
				}
				if (q->cost[_con4_NT] == 0) {
					p->cost[_con4_NT] = 0;
					p->rule._con4 = q->rule._con4;
				}
				if (q->cost[_conN_NT] == 0) {
					p->cost[_conN_NT] = 0;
					p->rule._conN = q->rule._conN;
				}
				if (q->cost[_addr_NT] == 0) {
					p->cost[_addr_NT] = 0;
					p->rule._addr = q->rule._addr;
				}
				if (q->cost[_faddr_NT] == 0) {
					p->cost[_faddr_NT] = 0;
					p->rule._faddr = q->rule._faddr;
				}
			}
			c = 0;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 5;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: INDIRP2(faddr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_faddr_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 26;
			_closure_reg(a, c + 0);
		}
		/* reg: INDIRP2(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 2;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 31;
			_closure_reg(a, c + 0);
		}
		break;
	case 2181: /* CVII2 */
		_label(LEFT_CHILD(a));
		/* reg: CVII2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 175;
			_closure_reg(a, c + 0);
		}
		break;
	case 2182: /* CVIU2 */
		_label(LEFT_CHILD(a));
		/* reg: CVIU2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 176;
			_closure_reg(a, c + 0);
		}
		break;
	case 2198: /* CVPU2 */
		_label(LEFT_CHILD(a));
		/* reg: CVPU2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 181;
			_closure_reg(a, c + 0);
		}
		break;
	case 2229: /* CVUI2 */
		_label(LEFT_CHILD(a));
		/* reg: CVUI2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 177;
			_closure_reg(a, c + 0);
		}
		break;
	case 2230: /* CVUU2 */
		_label(LEFT_CHILD(a));
		/* reg: CVUU2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 178;
			_closure_reg(a, c + 0);
		}
		break;
	case 2231: /* CVUP2 */
		_label(LEFT_CHILD(a));
		/* reg: CVUP2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 182;
			_closure_reg(a, c + 0);
		}
		break;
	case 2245: /* NEGI2 */
		_label(LEFT_CHILD(a));
		/* reg: NEGI2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 98;
			_closure_reg(a, c + 0);
		}
		break;
	case 2261: /* CALLI2 */
		_label(LEFT_CHILD(a));
		/* reg: CALLI2(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 5;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 191;
			_closure_reg(a, c + 0);
		}
		break;
	case 2262: /* CALLU2 */
		_label(LEFT_CHILD(a));
		/* reg: CALLU2(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 5;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 192;
			_closure_reg(a, c + 0);
		}
		break;
	case 2263: /* CALLP2 */
		_label(LEFT_CHILD(a));
		/* reg: CALLP2(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 5;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 193;
			_closure_reg(a, c + 0);
		}
		break;
	case 2277: /* LOADI2 */
		_label(LEFT_CHILD(a));
		/* reg: LOADI2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + (move(a));
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 199;
			_closure_reg(a, c + 0);
		}
		break;
	case 2278: /* LOADU2 */
		_label(LEFT_CHILD(a));
		/* reg: LOADU2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + (move(a));
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 200;
			_closure_reg(a, c + 0);
		}
		break;
	case 2279: /* LOADP2 */
		_label(LEFT_CHILD(a));
		/* reg: LOADP2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + (move(a));
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 201;
			_closure_reg(a, c + 0);
		}
		break;
	case 2293: /* RETI2 */
		_label(LEFT_CHILD(a));
		/* stmt: RETI2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 126;
		}
		break;
	case 2294: /* RETU2 */
		_label(LEFT_CHILD(a));
		/* stmt: RETU2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 127;
		}
		break;
	case 2295: /* RETP2 */
		_label(LEFT_CHILD(a));
		/* stmt: RETP2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 128;
		}
		break;
	case 2311: /* ADDRGP2 */
		/* addr: ADDRGP2 */
		if (0 + 0 < p->cost[_addr_NT]) {
			p->cost[_addr_NT] = 0 + 0;
			p->rule._addr = 1;
		}
		/* reg: ADDRGP2 */
		if (1 + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = 1 + 0;
			p->rule._reg = 19;
			_closure_reg(a, 1 + 0);
		}
		break;
	case 2327: /* ADDRFP2 */
		/* faddr: ADDRFP2 */
		if (0 + 0 < p->cost[_faddr_NT]) {
			p->cost[_faddr_NT] = 0 + 0;
			p->rule._faddr = 1;
			_closure_faddr(a, 0 + 0);
		}
		/* reg: ADDRFP2 */
		if (1 + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = 1 + 0;
			p->rule._reg = 20;
			_closure_reg(a, 1 + 0);
		}
		break;
	case 2343: /* ADDRLP2 */
		/* faddr: ADDRLP2 */
		if (0 + 0 < p->cost[_faddr_NT]) {
			p->cost[_faddr_NT] = 0 + 0;
			p->rule._faddr = 2;
			_closure_faddr(a, 0 + 0);
		}
		/* reg: ADDRLP2 */
		if (1 + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = 1 + 0;
			p->rule._reg = 21;
			_closure_reg(a, 1 + 0);
		}
		break;
	case 2357: /* ADDI2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: ADDI2(INDIRI2(VREGP),INDIRI2(VREGP)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			LEFT_CHILD(LEFT_CHILD(a))->op == 711 && /* VREGP */
			RIGHT_CHILD(a)->op == 2117 && /* INDIRI2 */
			LEFT_CHILD(RIGHT_CHILD(a))->op == 711 /* VREGP */
		) {
			c = 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 9;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDI2(INDIRI2(VREGP),con2) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			LEFT_CHILD(LEFT_CHILD(a))->op == 711 /* VREGP */
		) {
			c = ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 12;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDI2(INDIRI2(faddr),con2) */
			LEFT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 66;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDI2(INDIRI2(faddr),INDIRI2(faddr)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 69;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDI2(INDIRI2(addr),con2) */
			LEFT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 72;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDI2(INDIRI2(addr),INDIRI2(addr)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 74;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDI2(reg,INDIRI2(addr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 76;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDI2(reg,INDIRI2(faddr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 78;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: ADDI2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 81;
			_closure_reg(a, c + 0);
		}
		/* reg: ADDI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 83;
			_closure_reg(a, c + 0);
		}
		break;
	case 2358: /* ADDU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: ADDU2(INDIRU2(VREGP),INDIRU2(VREGP)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			LEFT_CHILD(LEFT_CHILD(a))->op == 711 && /* VREGP */
			RIGHT_CHILD(a)->op == 2118 && /* INDIRU2 */
			LEFT_CHILD(RIGHT_CHILD(a))->op == 711 /* VREGP */
		) {
			c = 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 10;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDU2(INDIRU2(VREGP),con2) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			LEFT_CHILD(LEFT_CHILD(a))->op == 711 /* VREGP */
		) {
			c = ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 13;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDU2(INDIRU2(faddr),con2) */
			LEFT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 67;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDU2(INDIRU2(faddr),INDIRU2(faddr)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 70;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDU2(INDIRU2(addr),con2) */
			LEFT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 73;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDU2(INDIRU2(addr),INDIRU2(addr)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 75;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDU2(reg,INDIRU2(addr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 77;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDU2(reg,INDIRU2(faddr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 79;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: ADDU2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 82;
			_closure_reg(a, c + 0);
		}
		/* reg: ADDU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 84;
			_closure_reg(a, c + 0);
		}
		break;
	case 2359: /* ADDP2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: ADDP2(INDIRP2(VREGP),INDIRI2(VREGP)) */
			LEFT_CHILD(a)->op == 2119 && /* INDIRP2 */
			LEFT_CHILD(LEFT_CHILD(a))->op == 711 && /* VREGP */
			RIGHT_CHILD(a)->op == 2117 && /* INDIRI2 */
			LEFT_CHILD(RIGHT_CHILD(a))->op == 711 /* VREGP */
		) {
			c = 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 11;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDP2(INDIRP2(faddr),con2) */
			LEFT_CHILD(a)->op == 2119 /* INDIRP2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 68;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDP2(INDIRP2(faddr),INDIRI2(faddr)) */
			LEFT_CHILD(a)->op == 2119 && /* INDIRP2 */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 71;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDP2(reg,INDIRP2(faddr)) */
			RIGHT_CHILD(a)->op == 2119 /* INDIRP2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 80;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: ADDP2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 85;
			_closure_reg(a, c + 0);
		}
		/* addr: ADDP2(addr,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_addr_NT]) {
			p->cost[_addr_NT] = c + 0;
			p->rule._addr = 4;
		}
		break;
	case 2373: /* SUBI2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: SUBI2(INDIRI2(faddr),con2) */
			LEFT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 86;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: SUBI2(INDIRI2(faddr),INDIRI2(faddr)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 88;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: SUBI2(INDIRI2(addr),con2) */
			LEFT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 90;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: SUBI2(reg,INDIRI2(faddr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 5;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 92;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: SUBI2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 4;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 94;
			_closure_reg(a, c + 0);
		}
		/* reg: SUBI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 96;
			_closure_reg(a, c + 0);
		}
		break;
	case 2374: /* SUBU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: SUBU2(INDIRU2(faddr),con2) */
			LEFT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 87;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: SUBU2(INDIRU2(faddr),INDIRU2(faddr)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 89;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: SUBU2(INDIRU2(addr),con2) */
			LEFT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 91;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: SUBU2(reg,INDIRU2(faddr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 5;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 93;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: SUBU2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 4;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 95;
			_closure_reg(a, c + 0);
		}
		/* reg: SUBU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 97;
			_closure_reg(a, c + 0);
		}
		break;
	case 2389: /* LSHI2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: LSHI2(reg,conN) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_conN_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 155;
			_closure_reg(a, c + 0);
		}
		/* reg: LSHI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 15;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 159;
			_closure_reg(a, c + 0);
		}
		break;
	case 2390: /* LSHU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: LSHU2(reg,conN) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_conN_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 156;
			_closure_reg(a, c + 0);
		}
		/* reg: LSHU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 15;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 160;
			_closure_reg(a, c + 0);
		}
		break;
	case 2405: /* MODI2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: MODI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 113;
			_closure_reg(a, c + 0);
		}
		break;
	case 2406: /* MODU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: MODU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 114;
			_closure_reg(a, c + 0);
		}
		break;
	case 2421: /* RSHI2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: RSHI2(reg,conN) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_conN_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 158;
			_closure_reg(a, c + 0);
		}
		/* reg: RSHI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 15;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 162;
			_closure_reg(a, c + 0);
		}
		break;
	case 2422: /* RSHU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: RSHU2(reg,conN) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_conN_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 157;
			_closure_reg(a, c + 0);
		}
		/* reg: RSHU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 15;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 161;
			_closure_reg(a, c + 0);
		}
		break;
	case 2437: /* BANDI2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: BANDI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 135;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BANDI2(INDIRI2(faddr),INDIRI2(faddr)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 137;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BANDI2(reg,INDIRI2(faddr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 139;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 2438: /* BANDU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: BANDU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 136;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BANDU2(INDIRU2(faddr),INDIRU2(faddr)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 138;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BANDU2(reg,INDIRU2(faddr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 140;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 2453: /* BCOMI2 */
		_label(LEFT_CHILD(a));
		/* reg: BCOMI2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 153;
			_closure_reg(a, c + 0);
		}
		break;
	case 2454: /* BCOMU2 */
		_label(LEFT_CHILD(a));
		/* reg: BCOMU2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 154;
			_closure_reg(a, c + 0);
		}
		break;
	case 2469: /* BORI2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: BORI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 141;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BORI2(INDIRI2(faddr),INDIRI2(faddr)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 143;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BORI2(reg,INDIRI2(faddr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 145;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 2470: /* BORU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: BORU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 142;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BORU2(INDIRU2(faddr),INDIRU2(faddr)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 144;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BORU2(reg,INDIRU2(faddr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 146;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 2485: /* BXORI2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: BXORI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 147;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BXORI2(INDIRI2(faddr),INDIRI2(faddr)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 149;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BXORI2(reg,INDIRI2(faddr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 151;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 2486: /* BXORU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: BXORU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 148;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BXORU2(INDIRU2(faddr),INDIRU2(faddr)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 150;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BXORU2(reg,INDIRU2(faddr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 152;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 2501: /* DIVI2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: DIVI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 109;
			_closure_reg(a, c + 0);
		}
		break;
	case 2502: /* DIVU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: DIVU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 110;
			_closure_reg(a, c + 0);
		}
		break;
	case 2517: /* MULI2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: MULI2(INDIRI2(VREGP),INDIRI2(VREGP)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			LEFT_CHILD(LEFT_CHILD(a))->op == 711 && /* VREGP */
			RIGHT_CHILD(a)->op == 2117 && /* INDIRI2 */
			LEFT_CHILD(RIGHT_CHILD(a))->op == 711 /* VREGP */
		) {
			c = 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 14;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: MULI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 105;
			_closure_reg(a, c + 0);
		}
		break;
	case 2518: /* MULU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: MULU2(INDIRU2(VREGP),INDIRU2(VREGP)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			LEFT_CHILD(LEFT_CHILD(a))->op == 711 && /* VREGP */
			RIGHT_CHILD(a)->op == 2118 && /* INDIRU2 */
			LEFT_CHILD(RIGHT_CHILD(a))->op == 711 /* VREGP */
		) {
			c = 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 15;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: MULU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 106;
			_closure_reg(a, c + 0);
		}
		break;
	case 2533: /* EQI2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* stmt: EQI2(INDIRI2(faddr),INDIRI2(faddr)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 55;
			}
		}
		if (	/* stmt: EQI2(reg,INDIRI2(faddr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 4;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 57;
			}
		}
		/* stmt: EQI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 59;
		}
		if (	/* stmt: EQI2(INDIRI2(faddr),con2) */
			LEFT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 2;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 107;
			}
		}
		/* stmt: EQI2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 109;
		}
		break;
	case 2534: /* EQU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* stmt: EQU2(INDIRU2(faddr),INDIRU2(faddr)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 56;
			}
		}
		if (	/* stmt: EQU2(reg,INDIRU2(faddr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 4;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 58;
			}
		}
		/* stmt: EQU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 60;
		}
		if (	/* stmt: EQU2(INDIRU2(faddr),con2) */
			LEFT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 2;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 108;
			}
		}
		/* stmt: EQU2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 110;
		}
		break;
	case 2549: /* GEI2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* stmt: GEI2(INDIRI2(faddr),INDIRI2(faddr)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 85;
			}
		}
		if (	/* stmt: GEI2(reg,INDIRI2(faddr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 4;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 87;
			}
		}
		/* stmt: GEI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 89;
		}
		if (	/* stmt: GEI2(INDIRI2(faddr),con2) */
			LEFT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 2;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 99;
			}
		}
		/* stmt: GEI2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 101;
		}
		break;
	case 2550: /* GEU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* stmt: GEU2(INDIRU2(faddr),INDIRU2(faddr)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 86;
			}
		}
		if (	/* stmt: GEU2(reg,INDIRU2(faddr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 4;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 88;
			}
		}
		/* stmt: GEU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 90;
		}
		if (	/* stmt: GEU2(INDIRU2(faddr),con2) */
			LEFT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 2;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 100;
			}
		}
		/* stmt: GEU2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 102;
		}
		break;
	case 2565: /* GTI2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* stmt: GTI2(INDIRI2(faddr),INDIRI2(faddr)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 79;
			}
		}
		if (	/* stmt: GTI2(reg,INDIRI2(faddr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 4;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 81;
			}
		}
		/* stmt: GTI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 83;
		}
		if (	/* stmt: GTI2(INDIRI2(faddr),con2) */
			LEFT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 2;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 95;
			}
		}
		/* stmt: GTI2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 97;
		}
		break;
	case 2566: /* GTU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* stmt: GTU2(INDIRU2(faddr),INDIRU2(faddr)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 80;
			}
		}
		if (	/* stmt: GTU2(reg,INDIRU2(faddr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 4;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 82;
			}
		}
		/* stmt: GTU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 84;
		}
		if (	/* stmt: GTU2(INDIRU2(faddr),con2) */
			LEFT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 2;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 96;
			}
		}
		/* stmt: GTU2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 98;
		}
		break;
	case 2581: /* LEI2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* stmt: LEI2(INDIRI2(faddr),INDIRI2(faddr)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 73;
			}
		}
		if (	/* stmt: LEI2(reg,INDIRI2(faddr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 4;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 75;
			}
		}
		/* stmt: LEI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 77;
		}
		if (	/* stmt: LEI2(INDIRI2(faddr),con2) */
			LEFT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 2;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 91;
			}
		}
		/* stmt: LEI2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 93;
		}
		break;
	case 2582: /* LEU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* stmt: LEU2(INDIRU2(faddr),INDIRU2(faddr)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 74;
			}
		}
		if (	/* stmt: LEU2(reg,INDIRU2(faddr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 4;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 76;
			}
		}
		/* stmt: LEU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 78;
		}
		if (	/* stmt: LEU2(INDIRU2(faddr),con2) */
			LEFT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 2;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 92;
			}
		}
		/* stmt: LEU2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 94;
		}
		break;
	case 2597: /* LTI2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* stmt: LTI2(INDIRI2(faddr),INDIRI2(faddr)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 67;
			}
		}
		if (	/* stmt: LTI2(reg,INDIRI2(faddr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 4;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 69;
			}
		}
		/* stmt: LTI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 71;
		}
		if (	/* stmt: LTI2(INDIRI2(faddr),con2) */
			LEFT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 2;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 103;
			}
		}
		/* stmt: LTI2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 105;
		}
		break;
	case 2598: /* LTU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* stmt: LTU2(INDIRU2(faddr),INDIRU2(faddr)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 68;
			}
		}
		if (	/* stmt: LTU2(reg,INDIRU2(faddr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 4;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 70;
			}
		}
		/* stmt: LTU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 72;
		}
		if (	/* stmt: LTU2(INDIRU2(faddr),con2) */
			LEFT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 2;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 104;
			}
		}
		/* stmt: LTU2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 106;
		}
		break;
	case 2613: /* NEI2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* stmt: NEI2(INDIRI2(faddr),INDIRI2(faddr)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 61;
			}
		}
		if (	/* stmt: NEI2(reg,INDIRI2(faddr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 4;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 63;
			}
		}
		/* stmt: NEI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 65;
		}
		if (	/* stmt: NEI2(INDIRI2(faddr),con2) */
			LEFT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 2;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 111;
			}
		}
		/* stmt: NEI2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 113;
		}
		break;
	case 2614: /* NEU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* stmt: NEU2(INDIRU2(faddr),INDIRU2(faddr)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 62;
			}
		}
		if (	/* stmt: NEU2(reg,INDIRU2(faddr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 4;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 64;
			}
		}
		/* stmt: NEU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 66;
		}
		if (	/* stmt: NEU2(INDIRU2(faddr),con2) */
			LEFT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 2;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 112;
			}
		}
		/* stmt: NEU2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 114;
		}
		break;
	case 4117: /* CNSTI4 */
		/* con4: CNSTI4 */
		if (0 + 0 < p->cost[_con4_NT]) {
			p->cost[_con4_NT] = 0 + 0;
			p->rule._con4 = 1;
			_closure_con4(a, 0 + 0);
		}
		break;
	case 4118: /* CNSTU4 */
		/* con4: CNSTU4 */
		if (0 + 0 < p->cost[_con4_NT]) {
			p->cost[_con4_NT] = 0 + 0;
			p->rule._con4 = 2;
			_closure_con4(a, 0 + 0);
		}
		break;
	case 4119: /* CNSTP4 */
		/* con4: CNSTP4 */
		if (0 + 0 < p->cost[_con4_NT]) {
			p->cost[_con4_NT] = 0 + 0;
			p->rule._con4 = 3;
			_closure_con4(a, 0 + 0);
		}
		break;
	case 4133: /* ARGI4 */
		_label(LEFT_CHILD(a));
		/* stmt: ARGI4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 2;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 120;
		}
		break;
	case 4134: /* ARGU4 */
		_label(LEFT_CHILD(a));
		/* stmt: ARGU4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 2;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 121;
		}
		break;
	case 4135: /* ARGP4 */
		_label(LEFT_CHILD(a));
		/* stmt: ARGP4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 2;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 122;
		}
		break;
	case 4149: /* ASGNI4 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* stmt: ASGNI4(VREGP,reg) */
			LEFT_CHILD(a)->op == 711 /* VREGP */
		) {
			c = ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 6;
			}
		}
		/* stmt: ASGNI4(addr,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 4;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 19;
		}
		break;
	case 4150: /* ASGNU4 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* stmt: ASGNU4(VREGP,reg) */
			LEFT_CHILD(a)->op == 711 /* VREGP */
		) {
			c = ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 7;
			}
		}
		/* stmt: ASGNU4(addr,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 4;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 20;
		}
		break;
	case 4151: /* ASGNP4 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* stmt: ASGNP4(VREGP,reg) */
			LEFT_CHILD(a)->op == 711 /* VREGP */
		) {
			c = ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
			if (c + 0 < p->cost[_stmt_NT]) {
				p->cost[_stmt_NT] = c + 0;
				p->rule._stmt = 8;
			}
		}
		/* stmt: ASGNP4(addr,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 4;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 21;
		}
		break;
	case 4165: /* INDIRI4 */
		_label(LEFT_CHILD(a));
		if (	/* reg: INDIRI4(VREGP) */
			LEFT_CHILD(a)->op == 711 /* VREGP */
		) {
			if (mayrecalc(a)) {
				struct _state *q = a->syms[RX]->u.t.cse->x.state;
				if (q->cost[_stmt_NT] == 0) {
					p->cost[_stmt_NT] = 0;
					p->rule._stmt = q->rule._stmt;
				}
				if (q->cost[_reg_NT] == 0) {
					p->cost[_reg_NT] = 0;
					p->rule._reg = q->rule._reg;
				}
				if (q->cost[_con2_NT] == 0) {
					p->cost[_con2_NT] = 0;
					p->rule._con2 = q->rule._con2;
				}
				if (q->cost[_con1_NT] == 0) {
					p->cost[_con1_NT] = 0;
					p->rule._con1 = q->rule._con1;
				}
				if (q->cost[_con4_NT] == 0) {
					p->cost[_con4_NT] = 0;
					p->rule._con4 = q->rule._con4;
				}
				if (q->cost[_conN_NT] == 0) {
					p->cost[_conN_NT] = 0;
					p->rule._conN = q->rule._conN;
				}
				if (q->cost[_addr_NT] == 0) {
					p->cost[_addr_NT] = 0;
					p->rule._addr = q->rule._addr;
				}
				if (q->cost[_faddr_NT] == 0) {
					p->cost[_faddr_NT] = 0;
					p->rule._faddr = q->rule._faddr;
				}
			}
			c = 0;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 6;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: INDIRI4(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 4;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 32;
			_closure_reg(a, c + 0);
		}
		break;
	case 4166: /* INDIRU4 */
		_label(LEFT_CHILD(a));
		if (	/* reg: INDIRU4(VREGP) */
			LEFT_CHILD(a)->op == 711 /* VREGP */
		) {
			if (mayrecalc(a)) {
				struct _state *q = a->syms[RX]->u.t.cse->x.state;
				if (q->cost[_stmt_NT] == 0) {
					p->cost[_stmt_NT] = 0;
					p->rule._stmt = q->rule._stmt;
				}
				if (q->cost[_reg_NT] == 0) {
					p->cost[_reg_NT] = 0;
					p->rule._reg = q->rule._reg;
				}
				if (q->cost[_con2_NT] == 0) {
					p->cost[_con2_NT] = 0;
					p->rule._con2 = q->rule._con2;
				}
				if (q->cost[_con1_NT] == 0) {
					p->cost[_con1_NT] = 0;
					p->rule._con1 = q->rule._con1;
				}
				if (q->cost[_con4_NT] == 0) {
					p->cost[_con4_NT] = 0;
					p->rule._con4 = q->rule._con4;
				}
				if (q->cost[_conN_NT] == 0) {
					p->cost[_conN_NT] = 0;
					p->rule._conN = q->rule._conN;
				}
				if (q->cost[_addr_NT] == 0) {
					p->cost[_addr_NT] = 0;
					p->rule._addr = q->rule._addr;
				}
				if (q->cost[_faddr_NT] == 0) {
					p->cost[_faddr_NT] = 0;
					p->rule._faddr = q->rule._faddr;
				}
			}
			c = 0;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 7;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: INDIRU4(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 4;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 33;
			_closure_reg(a, c + 0);
		}
		break;
	case 4167: /* INDIRP4 */
		_label(LEFT_CHILD(a));
		if (	/* reg: INDIRP4(VREGP) */
			LEFT_CHILD(a)->op == 711 /* VREGP */
		) {
			if (mayrecalc(a)) {
				struct _state *q = a->syms[RX]->u.t.cse->x.state;
				if (q->cost[_stmt_NT] == 0) {
					p->cost[_stmt_NT] = 0;
					p->rule._stmt = q->rule._stmt;
				}
				if (q->cost[_reg_NT] == 0) {
					p->cost[_reg_NT] = 0;
					p->rule._reg = q->rule._reg;
				}
				if (q->cost[_con2_NT] == 0) {
					p->cost[_con2_NT] = 0;
					p->rule._con2 = q->rule._con2;
				}
				if (q->cost[_con1_NT] == 0) {
					p->cost[_con1_NT] = 0;
					p->rule._con1 = q->rule._con1;
				}
				if (q->cost[_con4_NT] == 0) {
					p->cost[_con4_NT] = 0;
					p->rule._con4 = q->rule._con4;
				}
				if (q->cost[_conN_NT] == 0) {
					p->cost[_conN_NT] = 0;
					p->rule._conN = q->rule._conN;
				}
				if (q->cost[_addr_NT] == 0) {
					p->cost[_addr_NT] = 0;
					p->rule._addr = q->rule._addr;
				}
				if (q->cost[_faddr_NT] == 0) {
					p->cost[_faddr_NT] = 0;
					p->rule._faddr = q->rule._faddr;
				}
			}
			c = 0;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 8;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: INDIRP4(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 4;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 34;
			_closure_reg(a, c + 0);
		}
		break;
	case 4229: /* CVII4 */
		_label(LEFT_CHILD(a));
		/* reg: CVII4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 8;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 183;
			_closure_reg(a, c + 0);
		}
		break;
	case 4230: /* CVIU4 */
		_label(LEFT_CHILD(a));
		/* reg: CVIU4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 2;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 184;
			_closure_reg(a, c + 0);
		}
		break;
	case 4246: /* CVPU4 */
		_label(LEFT_CHILD(a));
		/* reg: CVPU4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 2;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 187;
			_closure_reg(a, c + 0);
		}
		break;
	case 4277: /* CVUI4 */
		_label(LEFT_CHILD(a));
		/* reg: CVUI4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 2;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 185;
			_closure_reg(a, c + 0);
		}
		break;
	case 4278: /* CVUU4 */
		_label(LEFT_CHILD(a));
		/* reg: CVUU4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 2;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 186;
			_closure_reg(a, c + 0);
		}
		break;
	case 4279: /* CVUP4 */
		_label(LEFT_CHILD(a));
		/* reg: CVUP4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 188;
			_closure_reg(a, c + 0);
		}
		break;
	case 4309: /* CALLI4 */
		_label(LEFT_CHILD(a));
		/* reg: CALLI4(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 8;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 194;
			_closure_reg(a, c + 0);
		}
		break;
	case 4310: /* CALLU4 */
		_label(LEFT_CHILD(a));
		/* reg: CALLU4(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 8;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 195;
			_closure_reg(a, c + 0);
		}
		break;
	case 4311: /* CALLP4 */
		_label(LEFT_CHILD(a));
		/* reg: CALLP4(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 8;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 196;
			_closure_reg(a, c + 0);
		}
		break;
	case 4325: /* LOADI4 */
		_label(LEFT_CHILD(a));
		/* reg: LOADI4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + (move(a));
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 202;
			_closure_reg(a, c + 0);
		}
		break;
	case 4326: /* LOADU4 */
		_label(LEFT_CHILD(a));
		/* reg: LOADU4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + (move(a));
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 203;
			_closure_reg(a, c + 0);
		}
		break;
	case 4327: /* LOADP4 */
		_label(LEFT_CHILD(a));
		/* reg: LOADP4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + (move(a));
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 204;
			_closure_reg(a, c + 0);
		}
		break;
	case 4341: /* RETI4 */
		_label(LEFT_CHILD(a));
		/* stmt: RETI4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 129;
		}
		break;
	case 4342: /* RETU4 */
		_label(LEFT_CHILD(a));
		/* stmt: RETU4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 130;
		}
		break;
	case 4343: /* RETP4 */
		_label(LEFT_CHILD(a));
		/* stmt: RETP4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
		if (c + 0 < p->cost[_stmt_NT]) {
			p->cost[_stmt_NT] = c + 0;
			p->rule._stmt = 131;
		}
		break;
	case 4359: /* ADDRGP4 */
		/* addr: ADDRGP4 */
		if (0 + 0 < p->cost[_addr_NT]) {
			p->cost[_addr_NT] = 0 + 0;
			p->rule._addr = 2;
		}
		break;
	case 4375: /* ADDRFP4 */
		/* faddr: ADDRFP4 */
		if (0 + 0 < p->cost[_faddr_NT]) {
			p->cost[_faddr_NT] = 0 + 0;
			p->rule._faddr = 3;
			_closure_faddr(a, 0 + 0);
		}
		break;
	case 4391: /* ADDRLP4 */
		/* faddr: ADDRLP4 */
		if (0 + 0 < p->cost[_faddr_NT]) {
			p->cost[_faddr_NT] = 0 + 0;
			p->rule._faddr = 4;
			_closure_faddr(a, 0 + 0);
		}
		break;
	case 4405: /* ADDI4 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: ADDI4(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 99;
			_closure_reg(a, c + 0);
		}
		break;
	case 4406: /* ADDU4 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: ADDU4(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 100;
			_closure_reg(a, c + 0);
		}
		break;
	case 4421: /* SUBI4 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: SUBI4(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 101;
			_closure_reg(a, c + 0);
		}
		break;
	case 4422: /* SUBU4 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: SUBU4(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 102;
			_closure_reg(a, c + 0);
		}
		break;
	default:
		fatal("_label", "Bad terminal %d\n", OP_LABEL(a));
	}
}

static void _kids(NODEPTR_TYPE p, int eruleno, NODEPTR_TYPE kids[]) {
	if (!p)
		fatal("_kids", "Null tree\n", 0);
	if (!kids)
		fatal("_kids", "Null kids\n", 0);
	switch (eruleno) {
	case 346: /* stmt: RETV */
	case 234: /* stmt: LABELV */
	case 46: /* reg: ADDRLP2 */
	case 45: /* reg: ADDRFP2 */
	case 44: /* reg: ADDRGP2 */
	case 42: /* faddr: ADDRLP4 */
	case 41: /* faddr: ADDRFP4 */
	case 40: /* faddr: ADDRLP2 */
	case 39: /* faddr: ADDRFP2 */
	case 38: /* addr: ADDRGP4 */
	case 37: /* addr: ADDRGP2 */
	case 33: /* conN: CNSTU1 */
	case 32: /* conN: CNSTI1 */
	case 31: /* con4: CNSTP4 */
	case 30: /* con4: CNSTU4 */
	case 29: /* con4: CNSTI4 */
	case 28: /* con2: CNSTP2 */
	case 27: /* con2: CNSTU2 */
	case 26: /* con2: CNSTI2 */
	case 25: /* con1: CNSTU1 */
	case 24: /* con1: CNSTI1 */
	case 15: /* reg: MULU2(INDIRU2(VREGP),INDIRU2(VREGP)) */
	case 14: /* reg: MULI2(INDIRI2(VREGP),INDIRI2(VREGP)) */
	case 11: /* reg: ADDP2(INDIRP2(VREGP),INDIRI2(VREGP)) */
	case 10: /* reg: ADDU2(INDIRU2(VREGP),INDIRU2(VREGP)) */
	case 9: /* reg: ADDI2(INDIRI2(VREGP),INDIRI2(VREGP)) */
	case 8: /* reg: INDIRP4(VREGP) */
	case 7: /* reg: INDIRU4(VREGP) */
	case 6: /* reg: INDIRI4(VREGP) */
	case 5: /* reg: INDIRP2(VREGP) */
	case 4: /* reg: INDIRU2(VREGP) */
	case 3: /* reg: INDIRI2(VREGP) */
	case 2: /* reg: INDIRU1(VREGP) */
	case 1: /* reg: INDIRI1(VREGP) */
		break;
	case 23: /* stmt: ASGNP4(VREGP,reg) */
	case 22: /* stmt: ASGNU4(VREGP,reg) */
	case 21: /* stmt: ASGNI4(VREGP,reg) */
	case 20: /* stmt: ASGNP2(VREGP,reg) */
	case 19: /* stmt: ASGNU2(VREGP,reg) */
	case 18: /* stmt: ASGNI2(VREGP,reg) */
	case 17: /* stmt: ASGNU1(VREGP,reg) */
	case 16: /* stmt: ASGNI1(VREGP,reg) */
	case 13: /* reg: ADDU2(INDIRU2(VREGP),con2) */
	case 12: /* reg: ADDI2(INDIRI2(VREGP),con2) */
		kids[0] = RIGHT_CHILD(p);
		break;
	case 355: /* stmt: reg */
	case 43: /* addr: faddr */
	case 36: /* reg: con4 */
	case 35: /* reg: con2 */
	case 34: /* reg: con1 */
		kids[0] = p;
		break;
	case 354: /* reg: LOADP4(reg) */
	case 353: /* reg: LOADU4(reg) */
	case 352: /* reg: LOADI4(reg) */
	case 351: /* reg: LOADP2(reg) */
	case 350: /* reg: LOADU2(reg) */
	case 349: /* reg: LOADI2(reg) */
	case 348: /* reg: LOADU1(reg) */
	case 347: /* reg: LOADI1(reg) */
	case 345: /* stmt: RETP4(reg) */
	case 344: /* stmt: RETU4(reg) */
	case 343: /* stmt: RETI4(reg) */
	case 342: /* stmt: RETP2(reg) */
	case 341: /* stmt: RETU2(reg) */
	case 340: /* stmt: RETI2(reg) */
	case 339: /* stmt: RETU1(reg) */
	case 338: /* stmt: RETI1(reg) */
	case 337: /* stmt: CALLV(addr) */
	case 336: /* reg: CALLP4(addr) */
	case 335: /* reg: CALLU4(addr) */
	case 334: /* reg: CALLI4(addr) */
	case 333: /* reg: CALLP2(addr) */
	case 332: /* reg: CALLU2(addr) */
	case 331: /* reg: CALLI2(addr) */
	case 330: /* reg: CALLU1(addr) */
	case 329: /* reg: CALLI1(addr) */
	case 328: /* stmt: ARGP4(reg) */
	case 327: /* stmt: ARGU4(reg) */
	case 326: /* stmt: ARGI4(reg) */
	case 325: /* stmt: ARGP2(reg) */
	case 324: /* stmt: ARGU2(reg) */
	case 323: /* stmt: ARGI2(reg) */
	case 322: /* stmt: ARGU1(reg) */
	case 321: /* stmt: ARGI1(reg) */
	case 236: /* stmt: JUMPV(reg) */
	case 235: /* stmt: JUMPV(addr) */
	case 233: /* reg: CVUP4(reg) */
	case 232: /* reg: CVPU4(reg) */
	case 231: /* reg: CVUU4(reg) */
	case 230: /* reg: CVUI4(reg) */
	case 229: /* reg: CVIU4(reg) */
	case 228: /* reg: CVII4(reg) */
	case 227: /* reg: CVUP2(reg) */
	case 226: /* reg: CVPU2(reg) */
	case 223: /* reg: CVUU2(reg) */
	case 222: /* reg: CVUI2(reg) */
	case 221: /* reg: CVIU2(reg) */
	case 220: /* reg: CVII2(reg) */
	case 219: /* reg: CVUU1(reg) */
	case 218: /* reg: CVUI1(reg) */
	case 217: /* reg: CVIU1(reg) */
	case 216: /* reg: CVII1(reg) */
	case 199: /* reg: BCOMU2(reg) */
	case 198: /* reg: BCOMI2(reg) */
	case 179: /* reg: BCOMU1(reg) */
	case 178: /* reg: BCOMI1(reg) */
	case 143: /* reg: NEGI2(reg) */
	case 109: /* reg: NEGI1(reg) */
	case 64: /* reg: INDIRP4(addr) */
	case 63: /* reg: INDIRU4(addr) */
	case 62: /* reg: INDIRI4(addr) */
	case 61: /* reg: INDIRP2(addr) */
	case 60: /* reg: INDIRU2(addr) */
	case 59: /* reg: INDIRI2(addr) */
	case 58: /* reg: INDIRU1(addr) */
	case 57: /* reg: INDIRI1(addr) */
	case 51: /* reg: INDIRP2(faddr) */
	case 50: /* reg: INDIRU2(faddr) */
	case 49: /* reg: INDIRI2(faddr) */
	case 48: /* reg: INDIRU1(faddr) */
	case 47: /* reg: INDIRI1(faddr) */
		kids[0] = LEFT_CHILD(p);
		break;
	case 320: /* stmt: NEU2(reg,con2) */
	case 319: /* stmt: NEI2(reg,con2) */
	case 316: /* stmt: EQU2(reg,con2) */
	case 315: /* stmt: EQI2(reg,con2) */
	case 312: /* stmt: LTU2(reg,con2) */
	case 311: /* stmt: LTI2(reg,con2) */
	case 308: /* stmt: GEU2(reg,con2) */
	case 307: /* stmt: GEI2(reg,con2) */
	case 304: /* stmt: GTU2(reg,con2) */
	case 303: /* stmt: GTI2(reg,con2) */
	case 300: /* stmt: LEU2(reg,con2) */
	case 299: /* stmt: LEI2(reg,con2) */
	case 296: /* stmt: GEU2(reg,reg) */
	case 295: /* stmt: GEI2(reg,reg) */
	case 290: /* stmt: GTU2(reg,reg) */
	case 289: /* stmt: GTI2(reg,reg) */
	case 284: /* stmt: LEU2(reg,reg) */
	case 283: /* stmt: LEI2(reg,reg) */
	case 278: /* stmt: LTU2(reg,reg) */
	case 277: /* stmt: LTI2(reg,reg) */
	case 272: /* stmt: NEU2(reg,reg) */
	case 271: /* stmt: NEI2(reg,reg) */
	case 266: /* stmt: EQU2(reg,reg) */
	case 265: /* stmt: EQI2(reg,reg) */
	case 259: /* stmt: GEU1(reg,reg) */
	case 257: /* stmt: GEI1(reg,reg) */
	case 255: /* stmt: GTU1(reg,reg) */
	case 253: /* stmt: GTI1(reg,reg) */
	case 251: /* stmt: LEU1(reg,reg) */
	case 249: /* stmt: LEI1(reg,reg) */
	case 247: /* stmt: LTU1(reg,reg) */
	case 245: /* stmt: LTI1(reg,reg) */
	case 242: /* stmt: NEU1(reg,reg) */
	case 241: /* stmt: NEI1(reg,reg) */
	case 238: /* stmt: EQU1(reg,reg) */
	case 237: /* stmt: EQI1(reg,reg) */
	case 215: /* reg: RSHI1(reg,reg) */
	case 214: /* reg: RSHU1(reg,reg) */
	case 213: /* reg: LSHU1(reg,reg) */
	case 212: /* reg: LSHI1(reg,reg) */
	case 211: /* reg: RSHI1(reg,conN) */
	case 210: /* reg: RSHU1(reg,conN) */
	case 209: /* reg: LSHU1(reg,conN) */
	case 208: /* reg: LSHI1(reg,conN) */
	case 207: /* reg: RSHI2(reg,reg) */
	case 206: /* reg: RSHU2(reg,reg) */
	case 205: /* reg: LSHU2(reg,reg) */
	case 204: /* reg: LSHI2(reg,reg) */
	case 203: /* reg: RSHI2(reg,conN) */
	case 202: /* reg: RSHU2(reg,conN) */
	case 201: /* reg: LSHU2(reg,conN) */
	case 200: /* reg: LSHI2(reg,conN) */
	case 193: /* reg: BXORU2(reg,reg) */
	case 192: /* reg: BXORI2(reg,reg) */
	case 187: /* reg: BORU2(reg,reg) */
	case 186: /* reg: BORI2(reg,reg) */
	case 181: /* reg: BANDU2(reg,reg) */
	case 180: /* reg: BANDI2(reg,reg) */
	case 175: /* reg: BXORU1(reg,reg) */
	case 174: /* reg: BXORI1(reg,reg) */
	case 169: /* reg: BORU1(reg,reg) */
	case 168: /* reg: BORI1(reg,reg) */
	case 163: /* reg: BANDU1(reg,reg) */
	case 162: /* reg: BANDI1(reg,reg) */
	case 159: /* reg: MODU2(reg,reg) */
	case 158: /* reg: MODI2(reg,reg) */
	case 157: /* reg: MODU1(reg,reg) */
	case 156: /* reg: MODI1(reg,reg) */
	case 155: /* reg: DIVU2(reg,reg) */
	case 154: /* reg: DIVI2(reg,reg) */
	case 153: /* reg: DIVU1(reg,reg) */
	case 152: /* reg: DIVI1(reg,reg) */
	case 151: /* reg: MULU2(reg,reg) */
	case 150: /* reg: MULI2(reg,reg) */
	case 149: /* reg: MULU1(reg,reg) */
	case 148: /* reg: MULI1(reg,reg) */
	case 147: /* reg: SUBU4(reg,reg) */
	case 146: /* reg: SUBI4(reg,reg) */
	case 145: /* reg: ADDU4(reg,reg) */
	case 144: /* reg: ADDI4(reg,reg) */
	case 142: /* reg: SUBU2(reg,reg) */
	case 141: /* reg: SUBI2(reg,reg) */
	case 140: /* reg: SUBU2(reg,con2) */
	case 139: /* reg: SUBI2(reg,con2) */
	case 130: /* addr: ADDP2(addr,reg) */
	case 129: /* reg: ADDP2(reg,reg) */
	case 128: /* reg: ADDU2(reg,reg) */
	case 127: /* reg: ADDI2(reg,reg) */
	case 126: /* reg: ADDU2(reg,con2) */
	case 125: /* reg: ADDI2(reg,con2) */
	case 108: /* reg: SUBU1(reg,conN) */
	case 107: /* reg: SUBI1(reg,conN) */
	case 103: /* reg: SUBU1(reg,reg) */
	case 102: /* reg: SUBI1(reg,reg) */
	case 96: /* reg: ADDU1(reg,conN) */
	case 95: /* reg: ADDI1(reg,conN) */
	case 91: /* reg: ADDU1(reg,reg) */
	case 90: /* reg: ADDI1(reg,reg) */
	case 72: /* stmt: ASGNP4(addr,reg) */
	case 71: /* stmt: ASGNU4(addr,reg) */
	case 70: /* stmt: ASGNI4(addr,reg) */
	case 69: /* stmt: ASGNP2(addr,reg) */
	case 68: /* stmt: ASGNU2(addr,reg) */
	case 67: /* stmt: ASGNI2(addr,reg) */
	case 66: /* stmt: ASGNU1(addr,reg) */
	case 65: /* stmt: ASGNI1(addr,reg) */
	case 56: /* stmt: ASGNP2(faddr,reg) */
	case 55: /* stmt: ASGNU2(faddr,reg) */
	case 54: /* stmt: ASGNI2(faddr,reg) */
	case 53: /* stmt: ASGNU1(faddr,reg) */
	case 52: /* stmt: ASGNI1(faddr,reg) */
		kids[0] = LEFT_CHILD(p);
		kids[1] = RIGHT_CHILD(p);
		break;
	case 78: /* reg: INDIRU1(ADDP2(reg,addr)) */
	case 77: /* reg: INDIRI1(ADDP2(reg,addr)) */
	case 76: /* reg: INDIRU1(ADDP2(addr,reg)) */
	case 75: /* reg: INDIRI1(ADDP2(addr,reg)) */
	case 74: /* reg: INDIRU1(ADDI2(addr,reg)) */
	case 73: /* reg: INDIRI1(ADDI2(addr,reg)) */
		kids[0] = LEFT_CHILD(LEFT_CHILD(p));
		kids[1] = RIGHT_CHILD(LEFT_CHILD(p));
		break;
	case 84: /* stmt: ASGNU1(ADDP2(reg,addr),reg) */
	case 83: /* stmt: ASGNI1(ADDP2(reg,addr),reg) */
	case 82: /* stmt: ASGNU1(ADDP2(addr,reg),reg) */
	case 81: /* stmt: ASGNI1(ADDP2(addr,reg),reg) */
	case 80: /* stmt: ASGNU1(ADDI2(addr,reg),reg) */
	case 79: /* stmt: ASGNI1(ADDI2(addr,reg),reg) */
		kids[0] = LEFT_CHILD(LEFT_CHILD(p));
		kids[1] = RIGHT_CHILD(LEFT_CHILD(p));
		kids[2] = RIGHT_CHILD(p);
		break;
	case 292: /* stmt: GEU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 291: /* stmt: GEI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 286: /* stmt: GTU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 285: /* stmt: GTI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 280: /* stmt: LEU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 279: /* stmt: LEI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 274: /* stmt: LTU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 273: /* stmt: LTI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 268: /* stmt: NEU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 267: /* stmt: NEI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 262: /* stmt: EQU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 261: /* stmt: EQI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 195: /* reg: BXORU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 194: /* reg: BXORI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 189: /* reg: BORU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 188: /* reg: BORI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 183: /* reg: BANDU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 182: /* reg: BANDI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 173: /* reg: BXORU1(INDIRU1(addr),INDIRU1(addr)) */
	case 172: /* reg: BXORI1(INDIRI1(addr),INDIRI1(addr)) */
	case 167: /* reg: BORU1(INDIRU1(addr),INDIRU1(addr)) */
	case 166: /* reg: BORI1(INDIRI1(addr),INDIRI1(addr)) */
	case 161: /* reg: BANDU1(INDIRU1(addr),INDIRU1(addr)) */
	case 160: /* reg: BANDI1(INDIRI1(addr),INDIRI1(addr)) */
	case 134: /* reg: SUBU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 133: /* reg: SUBI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 119: /* reg: ADDU2(INDIRU2(addr),INDIRU2(addr)) */
	case 118: /* reg: ADDI2(INDIRI2(addr),INDIRI2(addr)) */
	case 115: /* reg: ADDP2(INDIRP2(faddr),INDIRI2(faddr)) */
	case 114: /* reg: ADDU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 113: /* reg: ADDI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 99: /* reg: SUBI1(INDIRU1(addr),INDIRU1(addr)) */
	case 98: /* reg: SUBU1(INDIRU1(addr),INDIRU1(addr)) */
	case 97: /* reg: SUBI1(INDIRI1(addr),INDIRI1(addr)) */
	case 87: /* reg: ADDI1(INDIRU1(addr),INDIRU1(addr)) */
	case 86: /* reg: ADDU1(INDIRU1(addr),INDIRU1(addr)) */
	case 85: /* reg: ADDI1(INDIRI1(addr),INDIRI1(addr)) */
		kids[0] = LEFT_CHILD(LEFT_CHILD(p));
		kids[1] = LEFT_CHILD(RIGHT_CHILD(p));
		break;
	case 101: /* reg: SUBU1(LOADU1(INDIRU1(addr)),LOADU1(INDIRU1(addr))) */
	case 100: /* reg: SUBI1(LOADI1(INDIRU1(addr)),LOADI1(INDIRU1(addr))) */
	case 89: /* reg: ADDU1(LOADU1(INDIRU1(addr)),LOADU1(INDIRU1(addr))) */
	case 88: /* reg: ADDI1(LOADI1(INDIRU1(addr)),LOADI1(INDIRU1(addr))) */
		kids[0] = LEFT_CHILD(LEFT_CHILD(LEFT_CHILD(p)));
		kids[1] = LEFT_CHILD(LEFT_CHILD(RIGHT_CHILD(p)));
		break;
	case 294: /* stmt: GEU2(reg,INDIRU2(faddr)) */
	case 293: /* stmt: GEI2(reg,INDIRI2(faddr)) */
	case 288: /* stmt: GTU2(reg,INDIRU2(faddr)) */
	case 287: /* stmt: GTI2(reg,INDIRI2(faddr)) */
	case 282: /* stmt: LEU2(reg,INDIRU2(faddr)) */
	case 281: /* stmt: LEI2(reg,INDIRI2(faddr)) */
	case 276: /* stmt: LTU2(reg,INDIRU2(faddr)) */
	case 275: /* stmt: LTI2(reg,INDIRI2(faddr)) */
	case 270: /* stmt: NEU2(reg,INDIRU2(faddr)) */
	case 269: /* stmt: NEI2(reg,INDIRI2(faddr)) */
	case 264: /* stmt: EQU2(reg,INDIRU2(faddr)) */
	case 263: /* stmt: EQI2(reg,INDIRI2(faddr)) */
	case 260: /* stmt: GEU1(reg,INDIRU1(addr)) */
	case 258: /* stmt: GEI1(reg,INDIRI1(addr)) */
	case 256: /* stmt: GTU1(reg,INDIRU1(addr)) */
	case 254: /* stmt: GTI1(reg,INDIRI1(addr)) */
	case 252: /* stmt: LEU1(reg,INDIRU1(addr)) */
	case 250: /* stmt: LEI1(reg,INDIRI1(addr)) */
	case 248: /* stmt: LTU1(reg,INDIRU1(addr)) */
	case 246: /* stmt: LTI1(reg,INDIRI1(addr)) */
	case 244: /* stmt: NEU1(reg,INDIRU1(addr)) */
	case 243: /* stmt: NEI1(reg,INDIRI1(addr)) */
	case 240: /* stmt: EQU1(reg,INDIRU1(addr)) */
	case 239: /* stmt: EQI1(reg,INDIRI1(addr)) */
	case 197: /* reg: BXORU2(reg,INDIRU2(faddr)) */
	case 196: /* reg: BXORI2(reg,INDIRI2(faddr)) */
	case 191: /* reg: BORU2(reg,INDIRU2(faddr)) */
	case 190: /* reg: BORI2(reg,INDIRI2(faddr)) */
	case 185: /* reg: BANDU2(reg,INDIRU2(faddr)) */
	case 184: /* reg: BANDI2(reg,INDIRI2(faddr)) */
	case 177: /* reg: BXORU1(reg,INDIRU1(addr)) */
	case 176: /* reg: BXORI1(reg,INDIRI1(addr)) */
	case 171: /* reg: BORU1(reg,INDIRU1(addr)) */
	case 170: /* reg: BORI1(reg,INDIRI1(addr)) */
	case 165: /* reg: BANDU1(reg,INDIRU1(addr)) */
	case 164: /* reg: BANDI1(reg,INDIRI1(addr)) */
	case 138: /* reg: SUBU2(reg,INDIRU2(faddr)) */
	case 137: /* reg: SUBI2(reg,INDIRI2(faddr)) */
	case 124: /* reg: ADDP2(reg,INDIRP2(faddr)) */
	case 123: /* reg: ADDU2(reg,INDIRU2(faddr)) */
	case 122: /* reg: ADDI2(reg,INDIRI2(faddr)) */
	case 121: /* reg: ADDU2(reg,INDIRU2(addr)) */
	case 120: /* reg: ADDI2(reg,INDIRI2(addr)) */
	case 106: /* reg: SUBI1(reg,INDIRU1(addr)) */
	case 105: /* reg: SUBU1(reg,INDIRU1(addr)) */
	case 104: /* reg: SUBI1(reg,INDIRI1(addr)) */
	case 94: /* reg: ADDI1(reg,INDIRU1(addr)) */
	case 93: /* reg: ADDU1(reg,INDIRU1(addr)) */
	case 92: /* reg: ADDI1(reg,INDIRI1(addr)) */
		kids[0] = LEFT_CHILD(p);
		kids[1] = LEFT_CHILD(RIGHT_CHILD(p));
		break;
	case 318: /* stmt: NEU2(INDIRU2(faddr),con2) */
	case 317: /* stmt: NEI2(INDIRI2(faddr),con2) */
	case 314: /* stmt: EQU2(INDIRU2(faddr),con2) */
	case 313: /* stmt: EQI2(INDIRI2(faddr),con2) */
	case 310: /* stmt: LTU2(INDIRU2(faddr),con2) */
	case 309: /* stmt: LTI2(INDIRI2(faddr),con2) */
	case 306: /* stmt: GEU2(INDIRU2(faddr),con2) */
	case 305: /* stmt: GEI2(INDIRI2(faddr),con2) */
	case 302: /* stmt: GTU2(INDIRU2(faddr),con2) */
	case 301: /* stmt: GTI2(INDIRI2(faddr),con2) */
	case 298: /* stmt: LEU2(INDIRU2(faddr),con2) */
	case 297: /* stmt: LEI2(INDIRI2(faddr),con2) */
	case 136: /* reg: SUBU2(INDIRU2(addr),con2) */
	case 135: /* reg: SUBI2(INDIRI2(addr),con2) */
	case 132: /* reg: SUBU2(INDIRU2(faddr),con2) */
	case 131: /* reg: SUBI2(INDIRI2(faddr),con2) */
	case 117: /* reg: ADDU2(INDIRU2(addr),con2) */
	case 116: /* reg: ADDI2(INDIRI2(addr),con2) */
	case 112: /* reg: ADDP2(INDIRP2(faddr),con2) */
	case 111: /* reg: ADDU2(INDIRU2(faddr),con2) */
	case 110: /* reg: ADDI2(INDIRI2(faddr),con2) */
		kids[0] = LEFT_CHILD(LEFT_CHILD(p));
		kids[1] = RIGHT_CHILD(p);
		break;
	case 225: /* reg: CVUU1(INDIRU2(addr)) */
	case 224: /* reg: CVII1(INDIRI2(addr)) */
		kids[0] = LEFT_CHILD(LEFT_CHILD(p));
		break;
	default:
		fatal("_kids", "Bad rule number %d\n", eruleno);
	}
}


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

    /* 3 temporary registers available: AC (bit 0), X (bit 1), Y (bit 2) */
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

static void function(Symbol f, Symbol caller[], Symbol callee[], int ncalls) {
    int i;
    int param_offset;

    /* Reset VREG slot mapping for each function */
    next_vreg_slot = 0;
    for (i = 0; i < MAX_VREG_SLOTS; i++) {
        vreg_symbols[i] = NULL;
    }

    print("\n; Function: %s\n", f->name);
    print("%s:\n", f->x.name);

    print("    ; Prologue\n");
    print("    PUSH_FP\n");
    print("    TSF\n");

    usedmask[IREG] = 0;
    freemask[IREG] = tmask[IREG];

    /* Parameters start at FP+4 (after saved FP and return address, both 16-bit) */
    param_offset = 4;
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

    switch (op) {
    case ASGN+I:
    case ASGN+U:
    case ASGN+P:
        /* Write to VREG - store to dedicated memory slot */
        if (LEFT_CHILD(p) && LEFT_CHILD(p)->op == VREG+P) {
            reg = LEFT_CHILD(p)->syms[0];
            if (reg) {
                slot = get_vreg_slot(reg);
                print("    STA _vreg%d\n", slot);
            }
        }
        break;
    case INDIR+I:
    case INDIR+U:
    case INDIR+P:
        /* Read from VREG - load from dedicated memory slot */
        if (LEFT_CHILD(p) && LEFT_CHILD(p)->op == VREG+P) {
            reg = LEFT_CHILD(p)->syms[0];
            if (reg) {
                slot = get_vreg_slot(reg);
                print("    LDA _vreg%d\n", slot);
            }
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
            if (generic(left->op) == INDIR && LEFT_CHILD(left) &&
                LEFT_CHILD(left)->op == VREG+P &&
                generic(right->op) == INDIR && LEFT_CHILD(right) &&
                LEFT_CHILD(right)->op == VREG+P) {
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
            else if (generic(left->op) == INDIR && LEFT_CHILD(left) &&
                     LEFT_CHILD(left)->op == VREG+P &&
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
            if (generic(left->op) == INDIR && LEFT_CHILD(left) &&
                LEFT_CHILD(left)->op == VREG+P &&
                generic(right->op) == INDIR && LEFT_CHILD(right) &&
                LEFT_CHILD(right)->op == VREG+P) {
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
