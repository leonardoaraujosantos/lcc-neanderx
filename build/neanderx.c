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

/*
generated at Sat Jan 17 20:40:55 2026
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
	_nts_0,	/* 16 */
	_nts_0,	/* 17 */
	_nts_0,	/* 18 */
	_nts_0,	/* 19 */
	_nts_0,	/* 20 */
	_nts_0,	/* 21 */
	_nts_0,	/* 22 */
	_nts_0,	/* 23 */
	_nts_2,	/* 24 */
	_nts_2,	/* 25 */
	_nts_2,	/* 26 */
	_nts_2,	/* 27 */
	_nts_2,	/* 28 */
	_nts_2,	/* 29 */
	_nts_2,	/* 30 */
	_nts_2,	/* 31 */
	_nts_0,	/* 32 */
	_nts_0,	/* 33 */
	_nts_0,	/* 34 */
	_nts_0,	/* 35 */
	_nts_0,	/* 36 */
	_nts_0,	/* 37 */
	_nts_0,	/* 38 */
	_nts_0,	/* 39 */
	_nts_0,	/* 40 */
	_nts_0,	/* 41 */
	_nts_3,	/* 42 */
	_nts_1,	/* 43 */
	_nts_4,	/* 44 */
	_nts_0,	/* 45 */
	_nts_0,	/* 46 */
	_nts_0,	/* 47 */
	_nts_0,	/* 48 */
	_nts_0,	/* 49 */
	_nts_0,	/* 50 */
	_nts_5,	/* 51 */
	_nts_0,	/* 52 */
	_nts_0,	/* 53 */
	_nts_0,	/* 54 */
	_nts_5,	/* 55 */
	_nts_5,	/* 56 */
	_nts_5,	/* 57 */
	_nts_5,	/* 58 */
	_nts_5,	/* 59 */
	_nts_6,	/* 60 */
	_nts_6,	/* 61 */
	_nts_6,	/* 62 */
	_nts_6,	/* 63 */
	_nts_6,	/* 64 */
	_nts_7,	/* 65 */
	_nts_7,	/* 66 */
	_nts_7,	/* 67 */
	_nts_7,	/* 68 */
	_nts_7,	/* 69 */
	_nts_7,	/* 70 */
	_nts_7,	/* 71 */
	_nts_7,	/* 72 */
	_nts_8,	/* 73 */
	_nts_8,	/* 74 */
	_nts_8,	/* 75 */
	_nts_8,	/* 76 */
	_nts_8,	/* 77 */
	_nts_8,	/* 78 */
	_nts_8,	/* 79 */
	_nts_8,	/* 80 */
	_nts_8,	/* 81 */
	_nts_8,	/* 82 */
	_nts_8,	/* 83 */
	_nts_8,	/* 84 */
	_nts_9,	/* 85 */
	_nts_9,	/* 86 */
	_nts_10,	/* 87 */
	_nts_10,	/* 88 */
	_nts_10,	/* 89 */
	_nts_10,	/* 90 */
	_nts_11,	/* 91 */
	_nts_11,	/* 92 */
	_nts_12,	/* 93 */
	_nts_12,	/* 94 */
	_nts_12,	/* 95 */
	_nts_12,	/* 96 */
	_nts_12,	/* 97 */
	_nts_13,	/* 98 */
	_nts_13,	/* 99 */
	_nts_9,	/* 100 */
	_nts_9,	/* 101 */
	_nts_9,	/* 102 */
	_nts_14,	/* 103 */
	_nts_14,	/* 104 */
	_nts_12,	/* 105 */
	_nts_12,	/* 106 */
	_nts_12,	/* 107 */
	_nts_12,	/* 108 */
	_nts_12,	/* 109 */
	_nts_13,	/* 110 */
	_nts_13,	/* 111 */
	_nts_9,	/* 112 */
	_nts_9,	/* 113 */
	_nts_9,	/* 114 */
	_nts_14,	/* 115 */
	_nts_14,	/* 116 */
	_nts_2,	/* 117 */
	_nts_15,	/* 118 */
	_nts_15,	/* 119 */
	_nts_15,	/* 120 */
	_nts_16,	/* 121 */
	_nts_16,	/* 122 */
	_nts_16,	/* 123 */
	_nts_17,	/* 124 */
	_nts_17,	/* 125 */
	_nts_12,	/* 126 */
	_nts_12,	/* 127 */
	_nts_9,	/* 128 */
	_nts_9,	/* 129 */
	_nts_18,	/* 130 */
	_nts_18,	/* 131 */
	_nts_18,	/* 132 */
	_nts_19,	/* 133 */
	_nts_19,	/* 134 */
	_nts_13,	/* 135 */
	_nts_13,	/* 136 */
	_nts_13,	/* 137 */
	_nts_8,	/* 138 */
	_nts_15,	/* 139 */
	_nts_15,	/* 140 */
	_nts_16,	/* 141 */
	_nts_16,	/* 142 */
	_nts_17,	/* 143 */
	_nts_17,	/* 144 */
	_nts_12,	/* 145 */
	_nts_12,	/* 146 */
	_nts_9,	/* 147 */
	_nts_9,	/* 148 */
	_nts_18,	/* 149 */
	_nts_18,	/* 150 */
	_nts_19,	/* 151 */
	_nts_19,	/* 152 */
	_nts_13,	/* 153 */
	_nts_13,	/* 154 */
	_nts_2,	/* 155 */
	_nts_13,	/* 156 */
	_nts_13,	/* 157 */
	_nts_13,	/* 158 */
	_nts_13,	/* 159 */
	_nts_13,	/* 160 */
	_nts_13,	/* 161 */
	_nts_13,	/* 162 */
	_nts_13,	/* 163 */
	_nts_13,	/* 164 */
	_nts_13,	/* 165 */
	_nts_13,	/* 166 */
	_nts_13,	/* 167 */
	_nts_16,	/* 168 */
	_nts_16,	/* 169 */
	_nts_18,	/* 170 */
	_nts_18,	/* 171 */
	_nts_13,	/* 172 */
	_nts_13,	/* 173 */
	_nts_13,	/* 174 */
	_nts_13,	/* 175 */
	_nts_16,	/* 176 */
	_nts_16,	/* 177 */
	_nts_18,	/* 178 */
	_nts_18,	/* 179 */
	_nts_12,	/* 180 */
	_nts_12,	/* 181 */
	_nts_13,	/* 182 */
	_nts_13,	/* 183 */
	_nts_9,	/* 184 */
	_nts_9,	/* 185 */
	_nts_12,	/* 186 */
	_nts_12,	/* 187 */
	_nts_13,	/* 188 */
	_nts_13,	/* 189 */
	_nts_9,	/* 190 */
	_nts_9,	/* 191 */
	_nts_12,	/* 192 */
	_nts_12,	/* 193 */
	_nts_13,	/* 194 */
	_nts_13,	/* 195 */
	_nts_9,	/* 196 */
	_nts_9,	/* 197 */
	_nts_2,	/* 198 */
	_nts_2,	/* 199 */
	_nts_13,	/* 200 */
	_nts_13,	/* 201 */
	_nts_16,	/* 202 */
	_nts_16,	/* 203 */
	_nts_18,	/* 204 */
	_nts_18,	/* 205 */
	_nts_12,	/* 206 */
	_nts_12,	/* 207 */
	_nts_19,	/* 208 */
	_nts_19,	/* 209 */
	_nts_15,	/* 210 */
	_nts_15,	/* 211 */
	_nts_9,	/* 212 */
	_nts_9,	/* 213 */
	_nts_13,	/* 214 */
	_nts_13,	/* 215 */
	_nts_16,	/* 216 */
	_nts_16,	/* 217 */
	_nts_18,	/* 218 */
	_nts_18,	/* 219 */
	_nts_12,	/* 220 */
	_nts_12,	/* 221 */
	_nts_19,	/* 222 */
	_nts_19,	/* 223 */
	_nts_15,	/* 224 */
	_nts_15,	/* 225 */
	_nts_9,	/* 226 */
	_nts_9,	/* 227 */
	_nts_13,	/* 228 */
	_nts_13,	/* 229 */
	_nts_16,	/* 230 */
	_nts_16,	/* 231 */
	_nts_18,	/* 232 */
	_nts_18,	/* 233 */
	_nts_12,	/* 234 */
	_nts_12,	/* 235 */
	_nts_19,	/* 236 */
	_nts_19,	/* 237 */
	_nts_15,	/* 238 */
	_nts_15,	/* 239 */
	_nts_9,	/* 240 */
	_nts_9,	/* 241 */
	_nts_2,	/* 242 */
	_nts_2,	/* 243 */
	_nts_14,	/* 244 */
	_nts_14,	/* 245 */
	_nts_14,	/* 246 */
	_nts_14,	/* 247 */
	_nts_13,	/* 248 */
	_nts_13,	/* 249 */
	_nts_13,	/* 250 */
	_nts_13,	/* 251 */
	_nts_14,	/* 252 */
	_nts_14,	/* 253 */
	_nts_14,	/* 254 */
	_nts_14,	/* 255 */
	_nts_13,	/* 256 */
	_nts_13,	/* 257 */
	_nts_13,	/* 258 */
	_nts_13,	/* 259 */
	_nts_2,	/* 260 */
	_nts_2,	/* 261 */
	_nts_2,	/* 262 */
	_nts_2,	/* 263 */
	_nts_2,	/* 264 */
	_nts_2,	/* 265 */
	_nts_2,	/* 266 */
	_nts_2,	/* 267 */
	_nts_7,	/* 268 */
	_nts_7,	/* 269 */
	_nts_2,	/* 270 */
	_nts_2,	/* 271 */
	_nts_2,	/* 272 */
	_nts_2,	/* 273 */
	_nts_2,	/* 274 */
	_nts_2,	/* 275 */
	_nts_2,	/* 276 */
	_nts_2,	/* 277 */
	_nts_0,	/* 278 */
	_nts_7,	/* 279 */
	_nts_2,	/* 280 */
	_nts_13,	/* 281 */
	_nts_13,	/* 282 */
	_nts_9,	/* 283 */
	_nts_9,	/* 284 */
	_nts_13,	/* 285 */
	_nts_13,	/* 286 */
	_nts_9,	/* 287 */
	_nts_9,	/* 288 */
	_nts_13,	/* 289 */
	_nts_9,	/* 290 */
	_nts_13,	/* 291 */
	_nts_9,	/* 292 */
	_nts_13,	/* 293 */
	_nts_9,	/* 294 */
	_nts_13,	/* 295 */
	_nts_9,	/* 296 */
	_nts_13,	/* 297 */
	_nts_9,	/* 298 */
	_nts_13,	/* 299 */
	_nts_9,	/* 300 */
	_nts_13,	/* 301 */
	_nts_9,	/* 302 */
	_nts_13,	/* 303 */
	_nts_9,	/* 304 */
	_nts_16,	/* 305 */
	_nts_16,	/* 306 */
	_nts_18,	/* 307 */
	_nts_18,	/* 308 */
	_nts_13,	/* 309 */
	_nts_13,	/* 310 */
	_nts_16,	/* 311 */
	_nts_16,	/* 312 */
	_nts_18,	/* 313 */
	_nts_18,	/* 314 */
	_nts_13,	/* 315 */
	_nts_13,	/* 316 */
	_nts_16,	/* 317 */
	_nts_16,	/* 318 */
	_nts_18,	/* 319 */
	_nts_18,	/* 320 */
	_nts_13,	/* 321 */
	_nts_13,	/* 322 */
	_nts_16,	/* 323 */
	_nts_16,	/* 324 */
	_nts_18,	/* 325 */
	_nts_18,	/* 326 */
	_nts_13,	/* 327 */
	_nts_13,	/* 328 */
	_nts_16,	/* 329 */
	_nts_16,	/* 330 */
	_nts_18,	/* 331 */
	_nts_18,	/* 332 */
	_nts_13,	/* 333 */
	_nts_13,	/* 334 */
	_nts_16,	/* 335 */
	_nts_16,	/* 336 */
	_nts_18,	/* 337 */
	_nts_18,	/* 338 */
	_nts_13,	/* 339 */
	_nts_13,	/* 340 */
	_nts_15,	/* 341 */
	_nts_15,	/* 342 */
	_nts_19,	/* 343 */
	_nts_19,	/* 344 */
	_nts_15,	/* 345 */
	_nts_15,	/* 346 */
	_nts_19,	/* 347 */
	_nts_19,	/* 348 */
	_nts_15,	/* 349 */
	_nts_15,	/* 350 */
	_nts_19,	/* 351 */
	_nts_19,	/* 352 */
	_nts_15,	/* 353 */
	_nts_15,	/* 354 */
	_nts_19,	/* 355 */
	_nts_19,	/* 356 */
	_nts_15,	/* 357 */
	_nts_15,	/* 358 */
	_nts_19,	/* 359 */
	_nts_19,	/* 360 */
	_nts_15,	/* 361 */
	_nts_15,	/* 362 */
	_nts_19,	/* 363 */
	_nts_19,	/* 364 */
	_nts_2,	/* 365 */
	_nts_2,	/* 366 */
	_nts_2,	/* 367 */
	_nts_2,	/* 368 */
	_nts_2,	/* 369 */
	_nts_2,	/* 370 */
	_nts_2,	/* 371 */
	_nts_2,	/* 372 */
	_nts_7,	/* 373 */
	_nts_7,	/* 374 */
	_nts_7,	/* 375 */
	_nts_7,	/* 376 */
	_nts_7,	/* 377 */
	_nts_7,	/* 378 */
	_nts_7,	/* 379 */
	_nts_7,	/* 380 */
	_nts_7,	/* 381 */
	_nts_2,	/* 382 */
	_nts_2,	/* 383 */
	_nts_2,	/* 384 */
	_nts_2,	/* 385 */
	_nts_2,	/* 386 */
	_nts_2,	/* 387 */
	_nts_2,	/* 388 */
	_nts_2,	/* 389 */
	_nts_0,	/* 390 */
	_nts_2,	/* 391 */
	_nts_2,	/* 392 */
	_nts_2,	/* 393 */
	_nts_2,	/* 394 */
	_nts_2,	/* 395 */
	_nts_2,	/* 396 */
	_nts_2,	/* 397 */
	_nts_2,	/* 398 */
	_nts_2,	/* 399 */
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
/* 16 */	"# sub vreg-vreg\n",	/* reg: SUBI2(INDIRI2(VREGP),INDIRI2(VREGP)) */
/* 17 */	"# sub vreg-vreg\n",	/* reg: SUBU2(INDIRU2(VREGP),INDIRU2(VREGP)) */
/* 18 */	"# xor vreg^vreg\n",	/* reg: BXORI2(INDIRI2(VREGP),INDIRI2(VREGP)) */
/* 19 */	"# xor vreg^vreg\n",	/* reg: BXORU2(INDIRU2(VREGP),INDIRU2(VREGP)) */
/* 20 */	"# and vreg&vreg\n",	/* reg: BANDI2(INDIRI2(VREGP),INDIRI2(VREGP)) */
/* 21 */	"# and vreg&vreg\n",	/* reg: BANDU2(INDIRU2(VREGP),INDIRU2(VREGP)) */
/* 22 */	"# or vreg|vreg\n",	/* reg: BORI2(INDIRI2(VREGP),INDIRI2(VREGP)) */
/* 23 */	"# or vreg|vreg\n",	/* reg: BORU2(INDIRU2(VREGP),INDIRU2(VREGP)) */
/* 24 */	"# write vreg\n",	/* stmt: ASGNI1(VREGP,reg) */
/* 25 */	"# write vreg\n",	/* stmt: ASGNU1(VREGP,reg) */
/* 26 */	"# write vreg\n",	/* stmt: ASGNI2(VREGP,reg) */
/* 27 */	"# write vreg\n",	/* stmt: ASGNU2(VREGP,reg) */
/* 28 */	"# write vreg\n",	/* stmt: ASGNP2(VREGP,reg) */
/* 29 */	"# write vreg\n",	/* stmt: ASGNI4(VREGP,reg) */
/* 30 */	"# write vreg\n",	/* stmt: ASGNU4(VREGP,reg) */
/* 31 */	"# write vreg\n",	/* stmt: ASGNP4(VREGP,reg) */
/* 32 */	"%a",	/* con1: CNSTI1 */
/* 33 */	"%a",	/* con1: CNSTU1 */
/* 34 */	"%a",	/* con2: CNSTI2 */
/* 35 */	"%a",	/* con2: CNSTU2 */
/* 36 */	"%a",	/* con2: CNSTP2 */
/* 37 */	"%a",	/* con4: CNSTI4 */
/* 38 */	"%a",	/* con4: CNSTU4 */
/* 39 */	"%a",	/* con4: CNSTP4 */
/* 40 */	"%a",	/* conN: CNSTI1 */
/* 41 */	"%a",	/* conN: CNSTU1 */
/* 42 */	"    LDI %0\n",	/* reg: con1 */
/* 43 */	"    LDI %0\n",	/* reg: con2 */
/* 44 */	"    LDI lo(%0)\n    PUSH\n    LDI hi(%0)\n",	/* reg: con4 */
/* 45 */	"%a",	/* addr: ADDRGP2 */
/* 46 */	"%a",	/* addr: ADDRGP4 */
/* 47 */	"%a,FP",	/* faddr: ADDRFP2 */
/* 48 */	"%a,FP",	/* faddr: ADDRLP2 */
/* 49 */	"%a,FP",	/* faddr: ADDRFP4 */
/* 50 */	"%a,FP",	/* faddr: ADDRLP4 */
/* 51 */	"%0",	/* addr: faddr */
/* 52 */	"    LDI %a\n",	/* reg: ADDRGP2 */
/* 53 */	"    LDI %a\n",	/* reg: ADDRFP2 */
/* 54 */	"    LDI %a\n",	/* reg: ADDRLP2 */
/* 55 */	"    LDA %0\n",	/* reg: INDIRI1(faddr) */
/* 56 */	"    LDA %0\n",	/* reg: INDIRU1(faddr) */
/* 57 */	"    LDA %0\n",	/* reg: INDIRI2(faddr) */
/* 58 */	"    LDA %0\n",	/* reg: INDIRU2(faddr) */
/* 59 */	"    LDA %0\n",	/* reg: INDIRP2(faddr) */
/* 60 */	"    STA %0\n",	/* stmt: ASGNI1(faddr,reg) */
/* 61 */	"    STA %0\n",	/* stmt: ASGNU1(faddr,reg) */
/* 62 */	"    STA %0\n",	/* stmt: ASGNI2(faddr,reg) */
/* 63 */	"    STA %0\n",	/* stmt: ASGNU2(faddr,reg) */
/* 64 */	"    STA %0\n",	/* stmt: ASGNP2(faddr,reg) */
/* 65 */	"    LDA %0\n",	/* reg: INDIRI1(addr) */
/* 66 */	"    LDA %0\n",	/* reg: INDIRU1(addr) */
/* 67 */	"    LDA %0\n",	/* reg: INDIRI2(addr) */
/* 68 */	"    LDA %0\n",	/* reg: INDIRU2(addr) */
/* 69 */	"    LDA %0\n",	/* reg: INDIRP2(addr) */
/* 70 */	"    LDA %0\n    PUSH\n    LDA %0+2\n",	/* reg: INDIRI4(addr) */
/* 71 */	"    LDA %0\n    PUSH\n    LDA %0+2\n",	/* reg: INDIRU4(addr) */
/* 72 */	"    LDA %0\n    PUSH\n    LDA %0+2\n",	/* reg: INDIRP4(addr) */
/* 73 */	"    STA %0\n",	/* stmt: ASGNI1(addr,reg) */
/* 74 */	"    STA %0\n",	/* stmt: ASGNU1(addr,reg) */
/* 75 */	"    STA %0\n",	/* stmt: ASGNI2(addr,reg) */
/* 76 */	"    STA %0\n",	/* stmt: ASGNU2(addr,reg) */
/* 77 */	"    STA %0\n",	/* stmt: ASGNP2(addr,reg) */
/* 78 */	"    STA %0+2\n    POP\n    STA %0\n",	/* stmt: ASGNI4(addr,reg) */
/* 79 */	"    STA %0+2\n    POP\n    STA %0\n",	/* stmt: ASGNU4(addr,reg) */
/* 80 */	"    STA %0+2\n    POP\n    STA %0\n",	/* stmt: ASGNP4(addr,reg) */
/* 81 */	"    TAX\n    LDA %0,X\n",	/* reg: INDIRI1(ADDI2(addr,reg)) */
/* 82 */	"    TAX\n    LDA %0,X\n",	/* reg: INDIRU1(ADDI2(addr,reg)) */
/* 83 */	"    TAX\n    LDA %0,X\n",	/* reg: INDIRI1(ADDP2(addr,reg)) */
/* 84 */	"    TAX\n    LDA %0,X\n",	/* reg: INDIRU1(ADDP2(addr,reg)) */
/* 85 */	"    TAX\n    LDA %1,X\n",	/* reg: INDIRI1(ADDP2(reg,addr)) */
/* 86 */	"    TAX\n    LDA %1,X\n",	/* reg: INDIRU1(ADDP2(reg,addr)) */
/* 87 */	"    TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n",	/* stmt: ASGNI1(ADDI2(addr,reg),reg) */
/* 88 */	"    TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n",	/* stmt: ASGNU1(ADDI2(addr,reg),reg) */
/* 89 */	"    TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n",	/* stmt: ASGNI1(ADDP2(addr,reg),reg) */
/* 90 */	"    TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n",	/* stmt: ASGNU1(ADDP2(addr,reg),reg) */
/* 91 */	"    TAY\n    POP\n    TAX\n    TYA\n    STA %1,X\n",	/* stmt: ASGNI1(ADDP2(reg,addr),reg) */
/* 92 */	"    TAY\n    POP\n    TAX\n    TYA\n    STA %1,X\n",	/* stmt: ASGNU1(ADDP2(reg,addr),reg) */
/* 93 */	"    LDA %0\n    ADD %1\n",	/* reg: ADDI1(INDIRI1(addr),INDIRI1(addr)) */
/* 94 */	"    LDA %0\n    ADD %1\n",	/* reg: ADDU1(INDIRU1(addr),INDIRU1(addr)) */
/* 95 */	"    LDA %0\n    ADD %1\n",	/* reg: ADDI1(INDIRU1(addr),INDIRU1(addr)) */
/* 96 */	"    LDA %0\n    ADD %1\n",	/* reg: ADDI1(LOADI1(INDIRU1(addr)),LOADI1(INDIRU1(addr))) */
/* 97 */	"    LDA %0\n    ADD %1\n",	/* reg: ADDU1(LOADU1(INDIRU1(addr)),LOADU1(INDIRU1(addr))) */
/* 98 */	"    ADDX\n",	/* reg: ADDI1(reg,reg) */
/* 99 */	"    ADDX\n",	/* reg: ADDU1(reg,reg) */
/* 100 */	"    ADD %1\n",	/* reg: ADDI1(reg,INDIRI1(addr)) */
/* 101 */	"    ADD %1\n",	/* reg: ADDU1(reg,INDIRU1(addr)) */
/* 102 */	"    ADD %1\n",	/* reg: ADDI1(reg,INDIRU1(addr)) */
/* 103 */	"    INC\n",	/* reg: ADDI1(reg,conN) */
/* 104 */	"    INC\n",	/* reg: ADDU1(reg,conN) */
/* 105 */	"    LDA %0\n    SUB %1\n",	/* reg: SUBI1(INDIRI1(addr),INDIRI1(addr)) */
/* 106 */	"    LDA %0\n    SUB %1\n",	/* reg: SUBU1(INDIRU1(addr),INDIRU1(addr)) */
/* 107 */	"    LDA %0\n    SUB %1\n",	/* reg: SUBI1(INDIRU1(addr),INDIRU1(addr)) */
/* 108 */	"    LDA %0\n    SUB %1\n",	/* reg: SUBI1(LOADI1(INDIRU1(addr)),LOADI1(INDIRU1(addr))) */
/* 109 */	"    LDA %0\n    SUB %1\n",	/* reg: SUBU1(LOADU1(INDIRU1(addr)),LOADU1(INDIRU1(addr))) */
/* 110 */	"    SUBX\n",	/* reg: SUBI1(reg,reg) */
/* 111 */	"    SUBX\n",	/* reg: SUBU1(reg,reg) */
/* 112 */	"    SUB %1\n",	/* reg: SUBI1(reg,INDIRI1(addr)) */
/* 113 */	"    SUB %1\n",	/* reg: SUBU1(reg,INDIRU1(addr)) */
/* 114 */	"    SUB %1\n",	/* reg: SUBI1(reg,INDIRU1(addr)) */
/* 115 */	"    DEC\n",	/* reg: SUBI1(reg,conN) */
/* 116 */	"    DEC\n",	/* reg: SUBU1(reg,conN) */
/* 117 */	"    NEG\n",	/* reg: NEGI1(reg) */
/* 118 */	"    LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n",	/* reg: ADDI2(INDIRI2(faddr),con2) */
/* 119 */	"    LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n",	/* reg: ADDU2(INDIRU2(faddr),con2) */
/* 120 */	"    LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n",	/* reg: ADDP2(INDIRP2(faddr),con2) */
/* 121 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n",	/* reg: ADDI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 122 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n",	/* reg: ADDU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 123 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n",	/* reg: ADDP2(INDIRP2(faddr),INDIRI2(faddr)) */
/* 124 */	"    LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n",	/* reg: ADDI2(INDIRI2(addr),con2) */
/* 125 */	"    LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n",	/* reg: ADDU2(INDIRU2(addr),con2) */
/* 126 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n",	/* reg: ADDI2(INDIRI2(addr),INDIRI2(addr)) */
/* 127 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n",	/* reg: ADDU2(INDIRU2(addr),INDIRU2(addr)) */
/* 128 */	"    STA _tmp\n    LDA %1\n    ADD _tmp\n",	/* reg: ADDI2(reg,INDIRI2(addr)) */
/* 129 */	"    STA _tmp\n    LDA %1\n    ADD _tmp\n",	/* reg: ADDU2(reg,INDIRU2(addr)) */
/* 130 */	"    STA _tmp\n    LDA %1\n    ADD _tmp\n",	/* reg: ADDI2(reg,INDIRI2(faddr)) */
/* 131 */	"    STA _tmp\n    LDA %1\n    ADD _tmp\n",	/* reg: ADDU2(reg,INDIRU2(faddr)) */
/* 132 */	"    STA _tmp\n    LDA %1\n    ADD _tmp\n",	/* reg: ADDP2(reg,INDIRP2(faddr)) */
/* 133 */	"    STA _tmp\n    LDI %1\n    ADD _tmp\n",	/* reg: ADDI2(reg,con2) */
/* 134 */	"    STA _tmp\n    LDI %1\n    ADD _tmp\n",	/* reg: ADDU2(reg,con2) */
/* 135 */	"    STA _tmp\n    POP\n    ADD _tmp\n",	/* reg: ADDI2(reg,reg) */
/* 136 */	"    STA _tmp\n    POP\n    ADD _tmp\n",	/* reg: ADDU2(reg,reg) */
/* 137 */	"    STA _tmp\n    POP\n    ADD _tmp\n",	/* reg: ADDP2(reg,reg) */
/* 138 */	"%0",	/* addr: ADDP2(addr,reg) */
/* 139 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n",	/* reg: SUBI2(INDIRI2(faddr),con2) */
/* 140 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n",	/* reg: SUBU2(INDIRU2(faddr),con2) */
/* 141 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n",	/* reg: SUBI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 142 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n",	/* reg: SUBU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 143 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n",	/* reg: SUBI2(INDIRI2(addr),con2) */
/* 144 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n",	/* reg: SUBU2(INDIRU2(addr),con2) */
/* 145 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n",	/* reg: SUBI2(INDIRI2(addr),INDIRI2(addr)) */
/* 146 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n",	/* reg: SUBU2(INDIRU2(addr),INDIRU2(addr)) */
/* 147 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n",	/* reg: SUBI2(reg,INDIRI2(addr)) */
/* 148 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n",	/* reg: SUBU2(reg,INDIRU2(addr)) */
/* 149 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n",	/* reg: SUBI2(reg,INDIRI2(faddr)) */
/* 150 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n",	/* reg: SUBU2(reg,INDIRU2(faddr)) */
/* 151 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n",	/* reg: SUBI2(reg,con2) */
/* 152 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n",	/* reg: SUBU2(reg,con2) */
/* 153 */	"    STA _tmp\n    POP\n    SUB _tmp\n",	/* reg: SUBI2(reg,reg) */
/* 154 */	"    STA _tmp\n    POP\n    SUB _tmp\n",	/* reg: SUBU2(reg,reg) */
/* 155 */	"    NEG\n",	/* reg: NEGI2(reg) */
/* 156 */	"    STA _tmp\n    POP\n    STA _tmp_hi\n    POP\n    STA _tmp2_hi\n    POP\n    ADD _tmp\n    PUSH\n    LDA _tmp2_hi\n    ADC _tmp_hi\n",	/* reg: ADDI4(reg,reg) */
/* 157 */	"    STA _tmp\n    POP\n    STA _tmp_hi\n    POP\n    STA _tmp2_hi\n    POP\n    ADD _tmp\n    PUSH\n    LDA _tmp2_hi\n    ADC _tmp_hi\n",	/* reg: ADDU4(reg,reg) */
/* 158 */	"    STA _tmp\n    POP\n    STA _tmp_hi\n    POP\n    STA _tmp2_hi\n    POP\n    SUB _tmp\n    PUSH\n    LDA _tmp2_hi\n    SBC _tmp_hi\n",	/* reg: SUBI4(reg,reg) */
/* 159 */	"    STA _tmp\n    POP\n    STA _tmp_hi\n    POP\n    STA _tmp2_hi\n    POP\n    SUB _tmp\n    PUSH\n    LDA _tmp2_hi\n    SBC _tmp_hi\n",	/* reg: SUBU4(reg,reg) */
/* 160 */	"    TAX\n    POP\n    MUL\n",	/* reg: MULI1(reg,reg) */
/* 161 */	"    TAX\n    POP\n    MUL\n",	/* reg: MULU1(reg,reg) */
/* 162 */	"    TAX\n    POP\n    MUL\n",	/* reg: MULI2(reg,reg) */
/* 163 */	"    TAX\n    POP\n    MUL\n",	/* reg: MULU2(reg,reg) */
/* 164 */	"    TAX\n    POP\n    DIV\n",	/* reg: DIVI1(reg,reg) */
/* 165 */	"    TAX\n    POP\n    DIV\n",	/* reg: DIVU1(reg,reg) */
/* 166 */	"    TAX\n    POP\n    DIV\n",	/* reg: DIVI2(reg,reg) */
/* 167 */	"    TAX\n    POP\n    DIV\n",	/* reg: DIVU2(reg,reg) */
/* 168 */	"    LDA %1\n    TAX\n    LDA %0\n    DIV\n",	/* reg: DIVI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 169 */	"    LDA %1\n    TAX\n    LDA %0\n    DIV\n",	/* reg: DIVU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 170 */	"    STA _tmp\n    LDA %1\n    TAX\n    LDA _tmp\n    DIV\n",	/* reg: DIVI2(reg,INDIRI2(faddr)) */
/* 171 */	"    STA _tmp\n    LDA %1\n    TAX\n    LDA _tmp\n    DIV\n",	/* reg: DIVU2(reg,INDIRU2(faddr)) */
/* 172 */	"    TAX\n    POP\n    MOD\n",	/* reg: MODI1(reg,reg) */
/* 173 */	"    TAX\n    POP\n    MOD\n",	/* reg: MODU1(reg,reg) */
/* 174 */	"    TAX\n    POP\n    MOD\n",	/* reg: MODI2(reg,reg) */
/* 175 */	"    TAX\n    POP\n    MOD\n",	/* reg: MODU2(reg,reg) */
/* 176 */	"    LDA %1\n    TAX\n    LDA %0\n    MOD\n",	/* reg: MODI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 177 */	"    LDA %1\n    TAX\n    LDA %0\n    MOD\n",	/* reg: MODU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 178 */	"    STA _tmp\n    LDA %1\n    TAX\n    LDA _tmp\n    MOD\n",	/* reg: MODI2(reg,INDIRI2(faddr)) */
/* 179 */	"    STA _tmp\n    LDA %1\n    TAX\n    LDA _tmp\n    MOD\n",	/* reg: MODU2(reg,INDIRU2(faddr)) */
/* 180 */	"    LDA %0\n    AND %1\n",	/* reg: BANDI1(INDIRI1(addr),INDIRI1(addr)) */
/* 181 */	"    LDA %0\n    AND %1\n",	/* reg: BANDU1(INDIRU1(addr),INDIRU1(addr)) */
/* 182 */	"    ANDX\n",	/* reg: BANDI1(reg,reg) */
/* 183 */	"    ANDX\n",	/* reg: BANDU1(reg,reg) */
/* 184 */	"    AND %1\n",	/* reg: BANDI1(reg,INDIRI1(addr)) */
/* 185 */	"    AND %1\n",	/* reg: BANDU1(reg,INDIRU1(addr)) */
/* 186 */	"    LDA %0\n    OR %1\n",	/* reg: BORI1(INDIRI1(addr),INDIRI1(addr)) */
/* 187 */	"    LDA %0\n    OR %1\n",	/* reg: BORU1(INDIRU1(addr),INDIRU1(addr)) */
/* 188 */	"    ORX\n",	/* reg: BORI1(reg,reg) */
/* 189 */	"    ORX\n",	/* reg: BORU1(reg,reg) */
/* 190 */	"    OR %1\n",	/* reg: BORI1(reg,INDIRI1(addr)) */
/* 191 */	"    OR %1\n",	/* reg: BORU1(reg,INDIRU1(addr)) */
/* 192 */	"    LDA %0\n    XOR %1\n",	/* reg: BXORI1(INDIRI1(addr),INDIRI1(addr)) */
/* 193 */	"    LDA %0\n    XOR %1\n",	/* reg: BXORU1(INDIRU1(addr),INDIRU1(addr)) */
/* 194 */	"    XORX\n",	/* reg: BXORI1(reg,reg) */
/* 195 */	"    XORX\n",	/* reg: BXORU1(reg,reg) */
/* 196 */	"    XOR %1\n",	/* reg: BXORI1(reg,INDIRI1(addr)) */
/* 197 */	"    XOR %1\n",	/* reg: BXORU1(reg,INDIRU1(addr)) */
/* 198 */	"    NOT\n",	/* reg: BCOMI1(reg) */
/* 199 */	"    NOT\n",	/* reg: BCOMU1(reg) */
/* 200 */	"    STA _tmp\n    POP\n    AND _tmp\n",	/* reg: BANDI2(reg,reg) */
/* 201 */	"    STA _tmp\n    POP\n    AND _tmp\n",	/* reg: BANDU2(reg,reg) */
/* 202 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    AND _tmp\n",	/* reg: BANDI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 203 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    AND _tmp\n",	/* reg: BANDU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 204 */	"    STA _tmp\n    LDA %1\n    AND _tmp\n",	/* reg: BANDI2(reg,INDIRI2(faddr)) */
/* 205 */	"    STA _tmp\n    LDA %1\n    AND _tmp\n",	/* reg: BANDU2(reg,INDIRU2(faddr)) */
/* 206 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    AND _tmp\n",	/* reg: BANDI2(INDIRI2(addr),INDIRI2(addr)) */
/* 207 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    AND _tmp\n",	/* reg: BANDU2(INDIRU2(addr),INDIRU2(addr)) */
/* 208 */	"    STA _tmp\n    LDI %1\n    AND _tmp\n",	/* reg: BANDI2(reg,con2) */
/* 209 */	"    STA _tmp\n    LDI %1\n    AND _tmp\n",	/* reg: BANDU2(reg,con2) */
/* 210 */	"    LDA %0\n    STA _tmp\n    LDI %1\n    AND _tmp\n",	/* reg: BANDI2(INDIRI2(faddr),con2) */
/* 211 */	"    LDA %0\n    STA _tmp\n    LDI %1\n    AND _tmp\n",	/* reg: BANDU2(INDIRU2(faddr),con2) */
/* 212 */	"    STA _tmp\n    LDA %1\n    AND _tmp\n",	/* reg: BANDI2(reg,INDIRI2(addr)) */
/* 213 */	"    STA _tmp\n    LDA %1\n    AND _tmp\n",	/* reg: BANDU2(reg,INDIRU2(addr)) */
/* 214 */	"    STA _tmp\n    POP\n    OR _tmp\n",	/* reg: BORI2(reg,reg) */
/* 215 */	"    STA _tmp\n    POP\n    OR _tmp\n",	/* reg: BORU2(reg,reg) */
/* 216 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    OR _tmp\n",	/* reg: BORI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 217 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    OR _tmp\n",	/* reg: BORU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 218 */	"    STA _tmp\n    LDA %1\n    OR _tmp\n",	/* reg: BORI2(reg,INDIRI2(faddr)) */
/* 219 */	"    STA _tmp\n    LDA %1\n    OR _tmp\n",	/* reg: BORU2(reg,INDIRU2(faddr)) */
/* 220 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    OR _tmp\n",	/* reg: BORI2(INDIRI2(addr),INDIRI2(addr)) */
/* 221 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    OR _tmp\n",	/* reg: BORU2(INDIRU2(addr),INDIRU2(addr)) */
/* 222 */	"    STA _tmp\n    LDI %1\n    OR _tmp\n",	/* reg: BORI2(reg,con2) */
/* 223 */	"    STA _tmp\n    LDI %1\n    OR _tmp\n",	/* reg: BORU2(reg,con2) */
/* 224 */	"    LDA %0\n    STA _tmp\n    LDI %1\n    OR _tmp\n",	/* reg: BORI2(INDIRI2(faddr),con2) */
/* 225 */	"    LDA %0\n    STA _tmp\n    LDI %1\n    OR _tmp\n",	/* reg: BORU2(INDIRU2(faddr),con2) */
/* 226 */	"    STA _tmp\n    LDA %1\n    OR _tmp\n",	/* reg: BORI2(reg,INDIRI2(addr)) */
/* 227 */	"    STA _tmp\n    LDA %1\n    OR _tmp\n",	/* reg: BORU2(reg,INDIRU2(addr)) */
/* 228 */	"    STA _tmp\n    POP\n    XOR _tmp\n",	/* reg: BXORI2(reg,reg) */
/* 229 */	"    STA _tmp\n    POP\n    XOR _tmp\n",	/* reg: BXORU2(reg,reg) */
/* 230 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    XOR _tmp\n",	/* reg: BXORI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 231 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    XOR _tmp\n",	/* reg: BXORU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 232 */	"    STA _tmp\n    LDA %1\n    XOR _tmp\n",	/* reg: BXORI2(reg,INDIRI2(faddr)) */
/* 233 */	"    STA _tmp\n    LDA %1\n    XOR _tmp\n",	/* reg: BXORU2(reg,INDIRU2(faddr)) */
/* 234 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    XOR _tmp\n",	/* reg: BXORI2(INDIRI2(addr),INDIRI2(addr)) */
/* 235 */	"    LDA %0\n    STA _tmp\n    LDA %1\n    XOR _tmp\n",	/* reg: BXORU2(INDIRU2(addr),INDIRU2(addr)) */
/* 236 */	"    STA _tmp\n    LDI %1\n    XOR _tmp\n",	/* reg: BXORI2(reg,con2) */
/* 237 */	"    STA _tmp\n    LDI %1\n    XOR _tmp\n",	/* reg: BXORU2(reg,con2) */
/* 238 */	"    LDA %0\n    STA _tmp\n    LDI %1\n    XOR _tmp\n",	/* reg: BXORI2(INDIRI2(faddr),con2) */
/* 239 */	"    LDA %0\n    STA _tmp\n    LDI %1\n    XOR _tmp\n",	/* reg: BXORU2(INDIRU2(faddr),con2) */
/* 240 */	"    STA _tmp\n    LDA %1\n    XOR _tmp\n",	/* reg: BXORI2(reg,INDIRI2(addr)) */
/* 241 */	"    STA _tmp\n    LDA %1\n    XOR _tmp\n",	/* reg: BXORU2(reg,INDIRU2(addr)) */
/* 242 */	"    NOT\n",	/* reg: BCOMI2(reg) */
/* 243 */	"    NOT\n",	/* reg: BCOMU2(reg) */
/* 244 */	"    SHL\n",	/* reg: LSHI2(reg,conN) */
/* 245 */	"    SHL\n",	/* reg: LSHU2(reg,conN) */
/* 246 */	"    SHR\n",	/* reg: RSHU2(reg,conN) */
/* 247 */	"    ASR\n",	/* reg: RSHI2(reg,conN) */
/* 248 */	"    TAX\n    POP\n    TAY\n_shl2_%a:\n    TXA\n    JZ _shl2d_%a\n    TYA\n    SHL\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shl2_%a\n_shl2d_%a:\n    TYA\n",	/* reg: LSHI2(reg,reg) */
/* 249 */	"    TAX\n    POP\n    TAY\n_shl2_%a:\n    TXA\n    JZ _shl2d_%a\n    TYA\n    SHL\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shl2_%a\n_shl2d_%a:\n    TYA\n",	/* reg: LSHU2(reg,reg) */
/* 250 */	"    TAX\n    POP\n    TAY\n_shr2_%a:\n    TXA\n    JZ _shr2d_%a\n    TYA\n    SHR\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shr2_%a\n_shr2d_%a:\n    TYA\n",	/* reg: RSHU2(reg,reg) */
/* 251 */	"    TAX\n    POP\n    TAY\n_asr2_%a:\n    TXA\n    JZ _asr2d_%a\n    TYA\n    ASR\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _asr2_%a\n_asr2d_%a:\n    TYA\n",	/* reg: RSHI2(reg,reg) */
/* 252 */	"    SHL\n",	/* reg: LSHI1(reg,conN) */
/* 253 */	"    SHL\n",	/* reg: LSHU1(reg,conN) */
/* 254 */	"    SHR\n",	/* reg: RSHU1(reg,conN) */
/* 255 */	"    ASR\n",	/* reg: RSHI1(reg,conN) */
/* 256 */	"    TAX\n    POP\n    TAY\n_shl_%a:\n    TXA\n    JZ _shld_%a\n    TYA\n    SHL\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shl_%a\n_shld_%a:\n    TYA\n",	/* reg: LSHI1(reg,reg) */
/* 257 */	"    TAX\n    POP\n    TAY\n_shl_%a:\n    TXA\n    JZ _shld_%a\n    TYA\n    SHL\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shl_%a\n_shld_%a:\n    TYA\n",	/* reg: LSHU1(reg,reg) */
/* 258 */	"    TAX\n    POP\n    TAY\n_shr_%a:\n    TXA\n    JZ _shrd_%a\n    TYA\n    SHR\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shr_%a\n_shrd_%a:\n    TYA\n",	/* reg: RSHU1(reg,reg) */
/* 259 */	"    TAX\n    POP\n    TAY\n_asr_%a:\n    TXA\n    JZ _asrd_%a\n    TYA\n    ASR\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _asr_%a\n_asrd_%a:\n    TYA\n",	/* reg: RSHI1(reg,reg) */
/* 260 */	"    AND _mask_ff\n",	/* reg: CVII1(reg) */
/* 261 */	"    AND _mask_ff\n",	/* reg: CVIU1(reg) */
/* 262 */	"    AND _mask_ff\n",	/* reg: CVUI1(reg) */
/* 263 */	"    AND _mask_ff\n",	/* reg: CVUU1(reg) */
/* 264 */	"; cvii2 - sign extend 8 to 16\n",	/* reg: CVII2(reg) */
/* 265 */	"; cviu2 - zero extend 8 to 16\n",	/* reg: CVIU2(reg) */
/* 266 */	"; cvui2 - already 16-bit\n",	/* reg: CVUI2(reg) */
/* 267 */	"; cvuu2 - already 16-bit\n",	/* reg: CVUU2(reg) */
/* 268 */	"    LDA %0\n    AND _mask_ff\n",	/* reg: CVII1(INDIRI2(addr)) */
/* 269 */	"    LDA %0\n    AND _mask_ff\n",	/* reg: CVUU1(INDIRU2(addr)) */
/* 270 */	"; cvpu2\n",	/* reg: CVPU2(reg) */
/* 271 */	"; cvup2\n",	/* reg: CVUP2(reg) */
/* 272 */	"    TAY\n    JN _sx4_%a\n    LDI 0\n    JMP _sx4d_%a\n_sx4_%a:\n    LDI 0xFFFF\n_sx4d_%a:\n    PUSH\n    TYA\n",	/* reg: CVII4(reg) */
/* 273 */	"    PUSH\n    LDI 0\n",	/* reg: CVIU4(reg) */
/* 274 */	"    PUSH\n    LDI 0\n",	/* reg: CVUI4(reg) */
/* 275 */	"    PUSH\n    LDI 0\n",	/* reg: CVUU4(reg) */
/* 276 */	"    PUSH\n    LDI 0\n",	/* reg: CVPU4(reg) */
/* 277 */	"; cvup4 - truncate to pointer\n",	/* reg: CVUP4(reg) */
/* 278 */	"%a:\n",	/* stmt: LABELV */
/* 279 */	"    JMP %0\n",	/* stmt: JUMPV(addr) */
/* 280 */	"    JMP %0\n",	/* stmt: JUMPV(reg) */
/* 281 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQI1(reg,reg) */
/* 282 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQU1(reg,reg) */
/* 283 */	"    CMP %1\n    JZ %a\n",	/* stmt: EQI1(reg,INDIRI1(addr)) */
/* 284 */	"    CMP %1\n    JZ %a\n",	/* stmt: EQU1(reg,INDIRU1(addr)) */
/* 285 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEI1(reg,reg) */
/* 286 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEU1(reg,reg) */
/* 287 */	"    CMP %1\n    JNZ %a\n",	/* stmt: NEI1(reg,INDIRI1(addr)) */
/* 288 */	"    CMP %1\n    JNZ %a\n",	/* stmt: NEU1(reg,INDIRU1(addr)) */
/* 289 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JN %a\n",	/* stmt: LTI1(reg,reg) */
/* 290 */	"    CMP %1\n    JN %a\n",	/* stmt: LTI1(reg,INDIRI1(addr)) */
/* 291 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JC %a\n",	/* stmt: LTU1(reg,reg) */
/* 292 */	"    CMP %1\n    JC %a\n",	/* stmt: LTU1(reg,INDIRU1(addr)) */
/* 293 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JLE %a\n",	/* stmt: LEI1(reg,reg) */
/* 294 */	"    CMP %1\n    JLE %a\n",	/* stmt: LEI1(reg,INDIRI1(addr)) */
/* 295 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JBE %a\n",	/* stmt: LEU1(reg,reg) */
/* 296 */	"    CMP %1\n    JBE %a\n",	/* stmt: LEU1(reg,INDIRU1(addr)) */
/* 297 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JGT %a\n",	/* stmt: GTI1(reg,reg) */
/* 298 */	"    CMP %1\n    JGT %a\n",	/* stmt: GTI1(reg,INDIRI1(addr)) */
/* 299 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JA %a\n",	/* stmt: GTU1(reg,reg) */
/* 300 */	"    CMP %1\n    JA %a\n",	/* stmt: GTU1(reg,INDIRU1(addr)) */
/* 301 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JGE %a\n",	/* stmt: GEI1(reg,reg) */
/* 302 */	"    CMP %1\n    JGE %a\n",	/* stmt: GEI1(reg,INDIRI1(addr)) */
/* 303 */	"    TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JNC %a\n",	/* stmt: GEU1(reg,reg) */
/* 304 */	"    CMP %1\n    JNC %a\n",	/* stmt: GEU1(reg,INDIRU1(addr)) */
/* 305 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 306 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 307 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQI2(reg,INDIRI2(faddr)) */
/* 308 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQU2(reg,INDIRU2(faddr)) */
/* 309 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQI2(reg,reg) */
/* 310 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQU2(reg,reg) */
/* 311 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 312 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 313 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEI2(reg,INDIRI2(faddr)) */
/* 314 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEU2(reg,INDIRU2(faddr)) */
/* 315 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEI2(reg,reg) */
/* 316 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEU2(reg,reg) */
/* 317 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JN %a\n",	/* stmt: LTI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 318 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JC %a\n",	/* stmt: LTU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 319 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JN %a\n",	/* stmt: LTI2(reg,INDIRI2(faddr)) */
/* 320 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JC %a\n",	/* stmt: LTU2(reg,INDIRU2(faddr)) */
/* 321 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JN %a\n",	/* stmt: LTI2(reg,reg) */
/* 322 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JC %a\n",	/* stmt: LTU2(reg,reg) */
/* 323 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JLE %a\n",	/* stmt: LEI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 324 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JBE %a\n",	/* stmt: LEU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 325 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JLE %a\n",	/* stmt: LEI2(reg,INDIRI2(faddr)) */
/* 326 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JBE %a\n",	/* stmt: LEU2(reg,INDIRU2(faddr)) */
/* 327 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JLE %a\n",	/* stmt: LEI2(reg,reg) */
/* 328 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JBE %a\n",	/* stmt: LEU2(reg,reg) */
/* 329 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JGT %a\n",	/* stmt: GTI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 330 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JA %a\n",	/* stmt: GTU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 331 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JGT %a\n",	/* stmt: GTI2(reg,INDIRI2(faddr)) */
/* 332 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JA %a\n",	/* stmt: GTU2(reg,INDIRU2(faddr)) */
/* 333 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JGT %a\n",	/* stmt: GTI2(reg,reg) */
/* 334 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JA %a\n",	/* stmt: GTU2(reg,reg) */
/* 335 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JGE %a\n",	/* stmt: GEI2(INDIRI2(faddr),INDIRI2(faddr)) */
/* 336 */	"    LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNC %a\n",	/* stmt: GEU2(INDIRU2(faddr),INDIRU2(faddr)) */
/* 337 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JGE %a\n",	/* stmt: GEI2(reg,INDIRI2(faddr)) */
/* 338 */	"    STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNC %a\n",	/* stmt: GEU2(reg,INDIRU2(faddr)) */
/* 339 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JGE %a\n",	/* stmt: GEI2(reg,reg) */
/* 340 */	"    STA _tmp\n    POP\n    CMP _tmp\n    JNC %a\n",	/* stmt: GEU2(reg,reg) */
/* 341 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JLE %a\n",	/* stmt: LEI2(INDIRI2(faddr),con2) */
/* 342 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JBE %a\n",	/* stmt: LEU2(INDIRU2(faddr),con2) */
/* 343 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JLE %a\n",	/* stmt: LEI2(reg,con2) */
/* 344 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JBE %a\n",	/* stmt: LEU2(reg,con2) */
/* 345 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JGT %a\n",	/* stmt: GTI2(INDIRI2(faddr),con2) */
/* 346 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JA %a\n",	/* stmt: GTU2(INDIRU2(faddr),con2) */
/* 347 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JGT %a\n",	/* stmt: GTI2(reg,con2) */
/* 348 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JA %a\n",	/* stmt: GTU2(reg,con2) */
/* 349 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JGE %a\n",	/* stmt: GEI2(INDIRI2(faddr),con2) */
/* 350 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNC %a\n",	/* stmt: GEU2(INDIRU2(faddr),con2) */
/* 351 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JGE %a\n",	/* stmt: GEI2(reg,con2) */
/* 352 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNC %a\n",	/* stmt: GEU2(reg,con2) */
/* 353 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JN %a\n",	/* stmt: LTI2(INDIRI2(faddr),con2) */
/* 354 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JC %a\n",	/* stmt: LTU2(INDIRU2(faddr),con2) */
/* 355 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JN %a\n",	/* stmt: LTI2(reg,con2) */
/* 356 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JC %a\n",	/* stmt: LTU2(reg,con2) */
/* 357 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQI2(INDIRI2(faddr),con2) */
/* 358 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQU2(INDIRU2(faddr),con2) */
/* 359 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQI2(reg,con2) */
/* 360 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JZ %a\n",	/* stmt: EQU2(reg,con2) */
/* 361 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEI2(INDIRI2(faddr),con2) */
/* 362 */	"    LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEU2(INDIRU2(faddr),con2) */
/* 363 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEI2(reg,con2) */
/* 364 */	"    STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNZ %a\n",	/* stmt: NEU2(reg,con2) */
/* 365 */	"    PUSH\n",	/* stmt: ARGI1(reg) */
/* 366 */	"    PUSH\n",	/* stmt: ARGU1(reg) */
/* 367 */	"    PUSH\n",	/* stmt: ARGI2(reg) */
/* 368 */	"    PUSH\n",	/* stmt: ARGU2(reg) */
/* 369 */	"    PUSH\n",	/* stmt: ARGP2(reg) */
/* 370 */	"    PUSH\n    POP\n    PUSH\n    PUSH\n",	/* stmt: ARGI4(reg) */
/* 371 */	"    PUSH\n    POP\n    PUSH\n    PUSH\n",	/* stmt: ARGU4(reg) */
/* 372 */	"    PUSH\n    POP\n    PUSH\n    PUSH\n",	/* stmt: ARGP4(reg) */
/* 373 */	"    CALL %0\n",	/* reg: CALLI1(addr) */
/* 374 */	"    CALL %0\n",	/* reg: CALLU1(addr) */
/* 375 */	"    CALL %0\n",	/* reg: CALLI2(addr) */
/* 376 */	"    CALL %0\n",	/* reg: CALLU2(addr) */
/* 377 */	"    CALL %0\n",	/* reg: CALLP2(addr) */
/* 378 */	"    CALL %0\n",	/* reg: CALLI4(addr) */
/* 379 */	"    CALL %0\n",	/* reg: CALLU4(addr) */
/* 380 */	"    CALL %0\n",	/* reg: CALLP4(addr) */
/* 381 */	"    CALL %0\n",	/* stmt: CALLV(addr) */
/* 382 */	"; ret - value in AC\n",	/* stmt: RETI1(reg) */
/* 383 */	"; ret - value in AC\n",	/* stmt: RETU1(reg) */
/* 384 */	"; ret - value in AC\n",	/* stmt: RETI2(reg) */
/* 385 */	"; ret - value in AC\n",	/* stmt: RETU2(reg) */
/* 386 */	"; ret - value in AC\n",	/* stmt: RETP2(reg) */
/* 387 */	"; ret - 32-bit value in stack\n",	/* stmt: RETI4(reg) */
/* 388 */	"; ret - 32-bit value in stack\n",	/* stmt: RETU4(reg) */
/* 389 */	"; ret - 32-bit value in stack\n",	/* stmt: RETP4(reg) */
/* 390 */	"; ret void\n",	/* stmt: RETV */
/* 391 */	"",	/* reg: LOADI1(reg) */
/* 392 */	"",	/* reg: LOADU1(reg) */
/* 393 */	"",	/* reg: LOADI2(reg) */
/* 394 */	"",	/* reg: LOADU2(reg) */
/* 395 */	"",	/* reg: LOADP2(reg) */
/* 396 */	"",	/* reg: LOADI4(reg) */
/* 397 */	"",	/* reg: LOADU4(reg) */
/* 398 */	"",	/* reg: LOADP4(reg) */
/* 399 */	"",	/* stmt: reg */
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
/* 16 */	1,	/* # sub vreg-vreg\n */
/* 17 */	1,	/* # sub vreg-vreg\n */
/* 18 */	1,	/* # xor vreg^vreg\n */
/* 19 */	1,	/* # xor vreg^vreg\n */
/* 20 */	1,	/* # and vreg&vreg\n */
/* 21 */	1,	/* # and vreg&vreg\n */
/* 22 */	1,	/* # or vreg|vreg\n */
/* 23 */	1,	/* # or vreg|vreg\n */
/* 24 */	1,	/* # write vreg\n */
/* 25 */	1,	/* # write vreg\n */
/* 26 */	1,	/* # write vreg\n */
/* 27 */	1,	/* # write vreg\n */
/* 28 */	1,	/* # write vreg\n */
/* 29 */	1,	/* # write vreg\n */
/* 30 */	1,	/* # write vreg\n */
/* 31 */	1,	/* # write vreg\n */
/* 32 */	0,	/* %a */
/* 33 */	0,	/* %a */
/* 34 */	0,	/* %a */
/* 35 */	0,	/* %a */
/* 36 */	0,	/* %a */
/* 37 */	0,	/* %a */
/* 38 */	0,	/* %a */
/* 39 */	0,	/* %a */
/* 40 */	0,	/* %a */
/* 41 */	0,	/* %a */
/* 42 */	1,	/*     LDI %0\n */
/* 43 */	1,	/*     LDI %0\n */
/* 44 */	1,	/*     LDI lo(%0)\n    PUSH\n    LDI hi(%0)\n */
/* 45 */	0,	/* %a */
/* 46 */	0,	/* %a */
/* 47 */	0,	/* %a,FP */
/* 48 */	0,	/* %a,FP */
/* 49 */	0,	/* %a,FP */
/* 50 */	0,	/* %a,FP */
/* 51 */	0,	/* %0 */
/* 52 */	1,	/*     LDI %a\n */
/* 53 */	1,	/*     LDI %a\n */
/* 54 */	1,	/*     LDI %a\n */
/* 55 */	1,	/*     LDA %0\n */
/* 56 */	1,	/*     LDA %0\n */
/* 57 */	1,	/*     LDA %0\n */
/* 58 */	1,	/*     LDA %0\n */
/* 59 */	1,	/*     LDA %0\n */
/* 60 */	1,	/*     STA %0\n */
/* 61 */	1,	/*     STA %0\n */
/* 62 */	1,	/*     STA %0\n */
/* 63 */	1,	/*     STA %0\n */
/* 64 */	1,	/*     STA %0\n */
/* 65 */	1,	/*     LDA %0\n */
/* 66 */	1,	/*     LDA %0\n */
/* 67 */	1,	/*     LDA %0\n */
/* 68 */	1,	/*     LDA %0\n */
/* 69 */	1,	/*     LDA %0\n */
/* 70 */	1,	/*     LDA %0\n    PUSH\n    LDA %0+2\n */
/* 71 */	1,	/*     LDA %0\n    PUSH\n    LDA %0+2\n */
/* 72 */	1,	/*     LDA %0\n    PUSH\n    LDA %0+2\n */
/* 73 */	1,	/*     STA %0\n */
/* 74 */	1,	/*     STA %0\n */
/* 75 */	1,	/*     STA %0\n */
/* 76 */	1,	/*     STA %0\n */
/* 77 */	1,	/*     STA %0\n */
/* 78 */	1,	/*     STA %0+2\n    POP\n    STA %0\n */
/* 79 */	1,	/*     STA %0+2\n    POP\n    STA %0\n */
/* 80 */	1,	/*     STA %0+2\n    POP\n    STA %0\n */
/* 81 */	1,	/*     TAX\n    LDA %0,X\n */
/* 82 */	1,	/*     TAX\n    LDA %0,X\n */
/* 83 */	1,	/*     TAX\n    LDA %0,X\n */
/* 84 */	1,	/*     TAX\n    LDA %0,X\n */
/* 85 */	1,	/*     TAX\n    LDA %1,X\n */
/* 86 */	1,	/*     TAX\n    LDA %1,X\n */
/* 87 */	1,	/*     TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n */
/* 88 */	1,	/*     TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n */
/* 89 */	1,	/*     TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n */
/* 90 */	1,	/*     TAY\n    POP\n    TAX\n    TYA\n    STA %0,X\n */
/* 91 */	1,	/*     TAY\n    POP\n    TAX\n    TYA\n    STA %1,X\n */
/* 92 */	1,	/*     TAY\n    POP\n    TAX\n    TYA\n    STA %1,X\n */
/* 93 */	1,	/*     LDA %0\n    ADD %1\n */
/* 94 */	1,	/*     LDA %0\n    ADD %1\n */
/* 95 */	1,	/*     LDA %0\n    ADD %1\n */
/* 96 */	1,	/*     LDA %0\n    ADD %1\n */
/* 97 */	1,	/*     LDA %0\n    ADD %1\n */
/* 98 */	1,	/*     ADDX\n */
/* 99 */	1,	/*     ADDX\n */
/* 100 */	1,	/*     ADD %1\n */
/* 101 */	1,	/*     ADD %1\n */
/* 102 */	1,	/*     ADD %1\n */
/* 103 */	1,	/*     INC\n */
/* 104 */	1,	/*     INC\n */
/* 105 */	1,	/*     LDA %0\n    SUB %1\n */
/* 106 */	1,	/*     LDA %0\n    SUB %1\n */
/* 107 */	1,	/*     LDA %0\n    SUB %1\n */
/* 108 */	1,	/*     LDA %0\n    SUB %1\n */
/* 109 */	1,	/*     LDA %0\n    SUB %1\n */
/* 110 */	1,	/*     SUBX\n */
/* 111 */	1,	/*     SUBX\n */
/* 112 */	1,	/*     SUB %1\n */
/* 113 */	1,	/*     SUB %1\n */
/* 114 */	1,	/*     SUB %1\n */
/* 115 */	1,	/*     DEC\n */
/* 116 */	1,	/*     DEC\n */
/* 117 */	1,	/*     NEG\n */
/* 118 */	1,	/*     LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n */
/* 119 */	1,	/*     LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n */
/* 120 */	1,	/*     LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n */
/* 121 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n */
/* 122 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n */
/* 123 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n */
/* 124 */	1,	/*     LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n */
/* 125 */	1,	/*     LDA %0\n    STA _tmp\n    LDI %1\n    ADD _tmp\n */
/* 126 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n */
/* 127 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    ADD _tmp\n */
/* 128 */	1,	/*     STA _tmp\n    LDA %1\n    ADD _tmp\n */
/* 129 */	1,	/*     STA _tmp\n    LDA %1\n    ADD _tmp\n */
/* 130 */	1,	/*     STA _tmp\n    LDA %1\n    ADD _tmp\n */
/* 131 */	1,	/*     STA _tmp\n    LDA %1\n    ADD _tmp\n */
/* 132 */	1,	/*     STA _tmp\n    LDA %1\n    ADD _tmp\n */
/* 133 */	1,	/*     STA _tmp\n    LDI %1\n    ADD _tmp\n */
/* 134 */	1,	/*     STA _tmp\n    LDI %1\n    ADD _tmp\n */
/* 135 */	1,	/*     STA _tmp\n    POP\n    ADD _tmp\n */
/* 136 */	1,	/*     STA _tmp\n    POP\n    ADD _tmp\n */
/* 137 */	1,	/*     STA _tmp\n    POP\n    ADD _tmp\n */
/* 138 */	0,	/* %0 */
/* 139 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n */
/* 140 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n */
/* 141 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n */
/* 142 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n */
/* 143 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n */
/* 144 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n */
/* 145 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n */
/* 146 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    SUB _tmp\n */
/* 147 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n */
/* 148 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n */
/* 149 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n */
/* 150 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n */
/* 151 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n */
/* 152 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    SUB _tmp\n */
/* 153 */	1,	/*     STA _tmp\n    POP\n    SUB _tmp\n */
/* 154 */	1,	/*     STA _tmp\n    POP\n    SUB _tmp\n */
/* 155 */	1,	/*     NEG\n */
/* 156 */	1,	/*     STA _tmp\n    POP\n    STA _tmp_hi\n    POP\n    STA _tmp2_hi\n    POP\n    ADD _tmp\n    PUSH\n    LDA _tmp2_hi\n    ADC _tmp_hi\n */
/* 157 */	1,	/*     STA _tmp\n    POP\n    STA _tmp_hi\n    POP\n    STA _tmp2_hi\n    POP\n    ADD _tmp\n    PUSH\n    LDA _tmp2_hi\n    ADC _tmp_hi\n */
/* 158 */	1,	/*     STA _tmp\n    POP\n    STA _tmp_hi\n    POP\n    STA _tmp2_hi\n    POP\n    SUB _tmp\n    PUSH\n    LDA _tmp2_hi\n    SBC _tmp_hi\n */
/* 159 */	1,	/*     STA _tmp\n    POP\n    STA _tmp_hi\n    POP\n    STA _tmp2_hi\n    POP\n    SUB _tmp\n    PUSH\n    LDA _tmp2_hi\n    SBC _tmp_hi\n */
/* 160 */	1,	/*     TAX\n    POP\n    MUL\n */
/* 161 */	1,	/*     TAX\n    POP\n    MUL\n */
/* 162 */	1,	/*     TAX\n    POP\n    MUL\n */
/* 163 */	1,	/*     TAX\n    POP\n    MUL\n */
/* 164 */	1,	/*     TAX\n    POP\n    DIV\n */
/* 165 */	1,	/*     TAX\n    POP\n    DIV\n */
/* 166 */	1,	/*     TAX\n    POP\n    DIV\n */
/* 167 */	1,	/*     TAX\n    POP\n    DIV\n */
/* 168 */	1,	/*     LDA %1\n    TAX\n    LDA %0\n    DIV\n */
/* 169 */	1,	/*     LDA %1\n    TAX\n    LDA %0\n    DIV\n */
/* 170 */	1,	/*     STA _tmp\n    LDA %1\n    TAX\n    LDA _tmp\n    DIV\n */
/* 171 */	1,	/*     STA _tmp\n    LDA %1\n    TAX\n    LDA _tmp\n    DIV\n */
/* 172 */	1,	/*     TAX\n    POP\n    MOD\n */
/* 173 */	1,	/*     TAX\n    POP\n    MOD\n */
/* 174 */	1,	/*     TAX\n    POP\n    MOD\n */
/* 175 */	1,	/*     TAX\n    POP\n    MOD\n */
/* 176 */	1,	/*     LDA %1\n    TAX\n    LDA %0\n    MOD\n */
/* 177 */	1,	/*     LDA %1\n    TAX\n    LDA %0\n    MOD\n */
/* 178 */	1,	/*     STA _tmp\n    LDA %1\n    TAX\n    LDA _tmp\n    MOD\n */
/* 179 */	1,	/*     STA _tmp\n    LDA %1\n    TAX\n    LDA _tmp\n    MOD\n */
/* 180 */	1,	/*     LDA %0\n    AND %1\n */
/* 181 */	1,	/*     LDA %0\n    AND %1\n */
/* 182 */	1,	/*     ANDX\n */
/* 183 */	1,	/*     ANDX\n */
/* 184 */	1,	/*     AND %1\n */
/* 185 */	1,	/*     AND %1\n */
/* 186 */	1,	/*     LDA %0\n    OR %1\n */
/* 187 */	1,	/*     LDA %0\n    OR %1\n */
/* 188 */	1,	/*     ORX\n */
/* 189 */	1,	/*     ORX\n */
/* 190 */	1,	/*     OR %1\n */
/* 191 */	1,	/*     OR %1\n */
/* 192 */	1,	/*     LDA %0\n    XOR %1\n */
/* 193 */	1,	/*     LDA %0\n    XOR %1\n */
/* 194 */	1,	/*     XORX\n */
/* 195 */	1,	/*     XORX\n */
/* 196 */	1,	/*     XOR %1\n */
/* 197 */	1,	/*     XOR %1\n */
/* 198 */	1,	/*     NOT\n */
/* 199 */	1,	/*     NOT\n */
/* 200 */	1,	/*     STA _tmp\n    POP\n    AND _tmp\n */
/* 201 */	1,	/*     STA _tmp\n    POP\n    AND _tmp\n */
/* 202 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    AND _tmp\n */
/* 203 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    AND _tmp\n */
/* 204 */	1,	/*     STA _tmp\n    LDA %1\n    AND _tmp\n */
/* 205 */	1,	/*     STA _tmp\n    LDA %1\n    AND _tmp\n */
/* 206 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    AND _tmp\n */
/* 207 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    AND _tmp\n */
/* 208 */	1,	/*     STA _tmp\n    LDI %1\n    AND _tmp\n */
/* 209 */	1,	/*     STA _tmp\n    LDI %1\n    AND _tmp\n */
/* 210 */	1,	/*     LDA %0\n    STA _tmp\n    LDI %1\n    AND _tmp\n */
/* 211 */	1,	/*     LDA %0\n    STA _tmp\n    LDI %1\n    AND _tmp\n */
/* 212 */	1,	/*     STA _tmp\n    LDA %1\n    AND _tmp\n */
/* 213 */	1,	/*     STA _tmp\n    LDA %1\n    AND _tmp\n */
/* 214 */	1,	/*     STA _tmp\n    POP\n    OR _tmp\n */
/* 215 */	1,	/*     STA _tmp\n    POP\n    OR _tmp\n */
/* 216 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    OR _tmp\n */
/* 217 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    OR _tmp\n */
/* 218 */	1,	/*     STA _tmp\n    LDA %1\n    OR _tmp\n */
/* 219 */	1,	/*     STA _tmp\n    LDA %1\n    OR _tmp\n */
/* 220 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    OR _tmp\n */
/* 221 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    OR _tmp\n */
/* 222 */	1,	/*     STA _tmp\n    LDI %1\n    OR _tmp\n */
/* 223 */	1,	/*     STA _tmp\n    LDI %1\n    OR _tmp\n */
/* 224 */	1,	/*     LDA %0\n    STA _tmp\n    LDI %1\n    OR _tmp\n */
/* 225 */	1,	/*     LDA %0\n    STA _tmp\n    LDI %1\n    OR _tmp\n */
/* 226 */	1,	/*     STA _tmp\n    LDA %1\n    OR _tmp\n */
/* 227 */	1,	/*     STA _tmp\n    LDA %1\n    OR _tmp\n */
/* 228 */	1,	/*     STA _tmp\n    POP\n    XOR _tmp\n */
/* 229 */	1,	/*     STA _tmp\n    POP\n    XOR _tmp\n */
/* 230 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    XOR _tmp\n */
/* 231 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    XOR _tmp\n */
/* 232 */	1,	/*     STA _tmp\n    LDA %1\n    XOR _tmp\n */
/* 233 */	1,	/*     STA _tmp\n    LDA %1\n    XOR _tmp\n */
/* 234 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    XOR _tmp\n */
/* 235 */	1,	/*     LDA %0\n    STA _tmp\n    LDA %1\n    XOR _tmp\n */
/* 236 */	1,	/*     STA _tmp\n    LDI %1\n    XOR _tmp\n */
/* 237 */	1,	/*     STA _tmp\n    LDI %1\n    XOR _tmp\n */
/* 238 */	1,	/*     LDA %0\n    STA _tmp\n    LDI %1\n    XOR _tmp\n */
/* 239 */	1,	/*     LDA %0\n    STA _tmp\n    LDI %1\n    XOR _tmp\n */
/* 240 */	1,	/*     STA _tmp\n    LDA %1\n    XOR _tmp\n */
/* 241 */	1,	/*     STA _tmp\n    LDA %1\n    XOR _tmp\n */
/* 242 */	1,	/*     NOT\n */
/* 243 */	1,	/*     NOT\n */
/* 244 */	1,	/*     SHL\n */
/* 245 */	1,	/*     SHL\n */
/* 246 */	1,	/*     SHR\n */
/* 247 */	1,	/*     ASR\n */
/* 248 */	1,	/*     TAX\n    POP\n    TAY\n_shl2_%a:\n    TXA\n    JZ _shl2d_%a\n    TYA\n    SHL\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shl2_%a\n_shl2d_%a:\n    TYA\n */
/* 249 */	1,	/*     TAX\n    POP\n    TAY\n_shl2_%a:\n    TXA\n    JZ _shl2d_%a\n    TYA\n    SHL\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shl2_%a\n_shl2d_%a:\n    TYA\n */
/* 250 */	1,	/*     TAX\n    POP\n    TAY\n_shr2_%a:\n    TXA\n    JZ _shr2d_%a\n    TYA\n    SHR\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shr2_%a\n_shr2d_%a:\n    TYA\n */
/* 251 */	1,	/*     TAX\n    POP\n    TAY\n_asr2_%a:\n    TXA\n    JZ _asr2d_%a\n    TYA\n    ASR\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _asr2_%a\n_asr2d_%a:\n    TYA\n */
/* 252 */	1,	/*     SHL\n */
/* 253 */	1,	/*     SHL\n */
/* 254 */	1,	/*     SHR\n */
/* 255 */	1,	/*     ASR\n */
/* 256 */	1,	/*     TAX\n    POP\n    TAY\n_shl_%a:\n    TXA\n    JZ _shld_%a\n    TYA\n    SHL\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shl_%a\n_shld_%a:\n    TYA\n */
/* 257 */	1,	/*     TAX\n    POP\n    TAY\n_shl_%a:\n    TXA\n    JZ _shld_%a\n    TYA\n    SHL\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shl_%a\n_shld_%a:\n    TYA\n */
/* 258 */	1,	/*     TAX\n    POP\n    TAY\n_shr_%a:\n    TXA\n    JZ _shrd_%a\n    TYA\n    SHR\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _shr_%a\n_shrd_%a:\n    TYA\n */
/* 259 */	1,	/*     TAX\n    POP\n    TAY\n_asr_%a:\n    TXA\n    JZ _asrd_%a\n    TYA\n    ASR\n    TAY\n    TXA\n    DEC\n    TAX\n    JMP _asr_%a\n_asrd_%a:\n    TYA\n */
/* 260 */	1,	/*     AND _mask_ff\n */
/* 261 */	1,	/*     AND _mask_ff\n */
/* 262 */	1,	/*     AND _mask_ff\n */
/* 263 */	1,	/*     AND _mask_ff\n */
/* 264 */	1,	/* ; cvii2 - sign extend 8 to 16\n */
/* 265 */	1,	/* ; cviu2 - zero extend 8 to 16\n */
/* 266 */	1,	/* ; cvui2 - already 16-bit\n */
/* 267 */	1,	/* ; cvuu2 - already 16-bit\n */
/* 268 */	1,	/*     LDA %0\n    AND _mask_ff\n */
/* 269 */	1,	/*     LDA %0\n    AND _mask_ff\n */
/* 270 */	1,	/* ; cvpu2\n */
/* 271 */	1,	/* ; cvup2\n */
/* 272 */	1,	/*     TAY\n    JN _sx4_%a\n    LDI 0\n    JMP _sx4d_%a\n_sx4_%a:\n    LDI 0xFFFF\n_sx4d_%a:\n    PUSH\n    TYA\n */
/* 273 */	1,	/*     PUSH\n    LDI 0\n */
/* 274 */	1,	/*     PUSH\n    LDI 0\n */
/* 275 */	1,	/*     PUSH\n    LDI 0\n */
/* 276 */	1,	/*     PUSH\n    LDI 0\n */
/* 277 */	1,	/* ; cvup4 - truncate to pointer\n */
/* 278 */	1,	/* %a:\n */
/* 279 */	1,	/*     JMP %0\n */
/* 280 */	1,	/*     JMP %0\n */
/* 281 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JZ %a\n */
/* 282 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JZ %a\n */
/* 283 */	1,	/*     CMP %1\n    JZ %a\n */
/* 284 */	1,	/*     CMP %1\n    JZ %a\n */
/* 285 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JNZ %a\n */
/* 286 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JNZ %a\n */
/* 287 */	1,	/*     CMP %1\n    JNZ %a\n */
/* 288 */	1,	/*     CMP %1\n    JNZ %a\n */
/* 289 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JN %a\n */
/* 290 */	1,	/*     CMP %1\n    JN %a\n */
/* 291 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JC %a\n */
/* 292 */	1,	/*     CMP %1\n    JC %a\n */
/* 293 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JLE %a\n */
/* 294 */	1,	/*     CMP %1\n    JLE %a\n */
/* 295 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JBE %a\n */
/* 296 */	1,	/*     CMP %1\n    JBE %a\n */
/* 297 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JGT %a\n */
/* 298 */	1,	/*     CMP %1\n    JGT %a\n */
/* 299 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JA %a\n */
/* 300 */	1,	/*     CMP %1\n    JA %a\n */
/* 301 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JGE %a\n */
/* 302 */	1,	/*     CMP %1\n    JGE %a\n */
/* 303 */	1,	/*     TAX\n    POP\n    STA _tmp\n    TXA\n    CMP _tmp\n    JNC %a\n */
/* 304 */	1,	/*     CMP %1\n    JNC %a\n */
/* 305 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JZ %a\n */
/* 306 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JZ %a\n */
/* 307 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JZ %a\n */
/* 308 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JZ %a\n */
/* 309 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JZ %a\n */
/* 310 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JZ %a\n */
/* 311 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNZ %a\n */
/* 312 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNZ %a\n */
/* 313 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNZ %a\n */
/* 314 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNZ %a\n */
/* 315 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JNZ %a\n */
/* 316 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JNZ %a\n */
/* 317 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JN %a\n */
/* 318 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JC %a\n */
/* 319 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JN %a\n */
/* 320 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JC %a\n */
/* 321 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JN %a\n */
/* 322 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JC %a\n */
/* 323 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JLE %a\n */
/* 324 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JBE %a\n */
/* 325 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JLE %a\n */
/* 326 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JBE %a\n */
/* 327 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JLE %a\n */
/* 328 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JBE %a\n */
/* 329 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JGT %a\n */
/* 330 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JA %a\n */
/* 331 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JGT %a\n */
/* 332 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JA %a\n */
/* 333 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JGT %a\n */
/* 334 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JA %a\n */
/* 335 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JGE %a\n */
/* 336 */	1,	/*     LDA %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNC %a\n */
/* 337 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JGE %a\n */
/* 338 */	1,	/*     STA _tmp2\n    LDA %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNC %a\n */
/* 339 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JGE %a\n */
/* 340 */	1,	/*     STA _tmp\n    POP\n    CMP _tmp\n    JNC %a\n */
/* 341 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JLE %a\n */
/* 342 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JBE %a\n */
/* 343 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JLE %a\n */
/* 344 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JBE %a\n */
/* 345 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JGT %a\n */
/* 346 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JA %a\n */
/* 347 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JGT %a\n */
/* 348 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JA %a\n */
/* 349 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JGE %a\n */
/* 350 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNC %a\n */
/* 351 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JGE %a\n */
/* 352 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNC %a\n */
/* 353 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JN %a\n */
/* 354 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JC %a\n */
/* 355 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JN %a\n */
/* 356 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JC %a\n */
/* 357 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JZ %a\n */
/* 358 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JZ %a\n */
/* 359 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JZ %a\n */
/* 360 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JZ %a\n */
/* 361 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNZ %a\n */
/* 362 */	1,	/*     LDI %1\n    STA _tmp\n    LDA %0\n    CMP _tmp\n    JNZ %a\n */
/* 363 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNZ %a\n */
/* 364 */	1,	/*     STA _tmp2\n    LDI %1\n    STA _tmp\n    LDA _tmp2\n    CMP _tmp\n    JNZ %a\n */
/* 365 */	1,	/*     PUSH\n */
/* 366 */	1,	/*     PUSH\n */
/* 367 */	1,	/*     PUSH\n */
/* 368 */	1,	/*     PUSH\n */
/* 369 */	1,	/*     PUSH\n */
/* 370 */	1,	/*     PUSH\n    POP\n    PUSH\n    PUSH\n */
/* 371 */	1,	/*     PUSH\n    POP\n    PUSH\n    PUSH\n */
/* 372 */	1,	/*     PUSH\n    POP\n    PUSH\n    PUSH\n */
/* 373 */	1,	/*     CALL %0\n */
/* 374 */	1,	/*     CALL %0\n */
/* 375 */	1,	/*     CALL %0\n */
/* 376 */	1,	/*     CALL %0\n */
/* 377 */	1,	/*     CALL %0\n */
/* 378 */	1,	/*     CALL %0\n */
/* 379 */	1,	/*     CALL %0\n */
/* 380 */	1,	/*     CALL %0\n */
/* 381 */	1,	/*     CALL %0\n */
/* 382 */	1,	/* ; ret - value in AC\n */
/* 383 */	1,	/* ; ret - value in AC\n */
/* 384 */	1,	/* ; ret - value in AC\n */
/* 385 */	1,	/* ; ret - value in AC\n */
/* 386 */	1,	/* ; ret - value in AC\n */
/* 387 */	1,	/* ; ret - 32-bit value in stack\n */
/* 388 */	1,	/* ; ret - 32-bit value in stack\n */
/* 389 */	1,	/* ; ret - 32-bit value in stack\n */
/* 390 */	1,	/* ; ret void\n */
/* 391 */	0,	/*  */
/* 392 */	0,	/*  */
/* 393 */	0,	/*  */
/* 394 */	0,	/*  */
/* 395 */	0,	/*  */
/* 396 */	0,	/*  */
/* 397 */	0,	/*  */
/* 398 */	0,	/*  */
/* 399 */	0,	/*  */
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
/* 16 */	"reg: SUBI2(INDIRI2(VREGP),INDIRI2(VREGP))",
/* 17 */	"reg: SUBU2(INDIRU2(VREGP),INDIRU2(VREGP))",
/* 18 */	"reg: BXORI2(INDIRI2(VREGP),INDIRI2(VREGP))",
/* 19 */	"reg: BXORU2(INDIRU2(VREGP),INDIRU2(VREGP))",
/* 20 */	"reg: BANDI2(INDIRI2(VREGP),INDIRI2(VREGP))",
/* 21 */	"reg: BANDU2(INDIRU2(VREGP),INDIRU2(VREGP))",
/* 22 */	"reg: BORI2(INDIRI2(VREGP),INDIRI2(VREGP))",
/* 23 */	"reg: BORU2(INDIRU2(VREGP),INDIRU2(VREGP))",
/* 24 */	"stmt: ASGNI1(VREGP,reg)",
/* 25 */	"stmt: ASGNU1(VREGP,reg)",
/* 26 */	"stmt: ASGNI2(VREGP,reg)",
/* 27 */	"stmt: ASGNU2(VREGP,reg)",
/* 28 */	"stmt: ASGNP2(VREGP,reg)",
/* 29 */	"stmt: ASGNI4(VREGP,reg)",
/* 30 */	"stmt: ASGNU4(VREGP,reg)",
/* 31 */	"stmt: ASGNP4(VREGP,reg)",
/* 32 */	"con1: CNSTI1",
/* 33 */	"con1: CNSTU1",
/* 34 */	"con2: CNSTI2",
/* 35 */	"con2: CNSTU2",
/* 36 */	"con2: CNSTP2",
/* 37 */	"con4: CNSTI4",
/* 38 */	"con4: CNSTU4",
/* 39 */	"con4: CNSTP4",
/* 40 */	"conN: CNSTI1",
/* 41 */	"conN: CNSTU1",
/* 42 */	"reg: con1",
/* 43 */	"reg: con2",
/* 44 */	"reg: con4",
/* 45 */	"addr: ADDRGP2",
/* 46 */	"addr: ADDRGP4",
/* 47 */	"faddr: ADDRFP2",
/* 48 */	"faddr: ADDRLP2",
/* 49 */	"faddr: ADDRFP4",
/* 50 */	"faddr: ADDRLP4",
/* 51 */	"addr: faddr",
/* 52 */	"reg: ADDRGP2",
/* 53 */	"reg: ADDRFP2",
/* 54 */	"reg: ADDRLP2",
/* 55 */	"reg: INDIRI1(faddr)",
/* 56 */	"reg: INDIRU1(faddr)",
/* 57 */	"reg: INDIRI2(faddr)",
/* 58 */	"reg: INDIRU2(faddr)",
/* 59 */	"reg: INDIRP2(faddr)",
/* 60 */	"stmt: ASGNI1(faddr,reg)",
/* 61 */	"stmt: ASGNU1(faddr,reg)",
/* 62 */	"stmt: ASGNI2(faddr,reg)",
/* 63 */	"stmt: ASGNU2(faddr,reg)",
/* 64 */	"stmt: ASGNP2(faddr,reg)",
/* 65 */	"reg: INDIRI1(addr)",
/* 66 */	"reg: INDIRU1(addr)",
/* 67 */	"reg: INDIRI2(addr)",
/* 68 */	"reg: INDIRU2(addr)",
/* 69 */	"reg: INDIRP2(addr)",
/* 70 */	"reg: INDIRI4(addr)",
/* 71 */	"reg: INDIRU4(addr)",
/* 72 */	"reg: INDIRP4(addr)",
/* 73 */	"stmt: ASGNI1(addr,reg)",
/* 74 */	"stmt: ASGNU1(addr,reg)",
/* 75 */	"stmt: ASGNI2(addr,reg)",
/* 76 */	"stmt: ASGNU2(addr,reg)",
/* 77 */	"stmt: ASGNP2(addr,reg)",
/* 78 */	"stmt: ASGNI4(addr,reg)",
/* 79 */	"stmt: ASGNU4(addr,reg)",
/* 80 */	"stmt: ASGNP4(addr,reg)",
/* 81 */	"reg: INDIRI1(ADDI2(addr,reg))",
/* 82 */	"reg: INDIRU1(ADDI2(addr,reg))",
/* 83 */	"reg: INDIRI1(ADDP2(addr,reg))",
/* 84 */	"reg: INDIRU1(ADDP2(addr,reg))",
/* 85 */	"reg: INDIRI1(ADDP2(reg,addr))",
/* 86 */	"reg: INDIRU1(ADDP2(reg,addr))",
/* 87 */	"stmt: ASGNI1(ADDI2(addr,reg),reg)",
/* 88 */	"stmt: ASGNU1(ADDI2(addr,reg),reg)",
/* 89 */	"stmt: ASGNI1(ADDP2(addr,reg),reg)",
/* 90 */	"stmt: ASGNU1(ADDP2(addr,reg),reg)",
/* 91 */	"stmt: ASGNI1(ADDP2(reg,addr),reg)",
/* 92 */	"stmt: ASGNU1(ADDP2(reg,addr),reg)",
/* 93 */	"reg: ADDI1(INDIRI1(addr),INDIRI1(addr))",
/* 94 */	"reg: ADDU1(INDIRU1(addr),INDIRU1(addr))",
/* 95 */	"reg: ADDI1(INDIRU1(addr),INDIRU1(addr))",
/* 96 */	"reg: ADDI1(LOADI1(INDIRU1(addr)),LOADI1(INDIRU1(addr)))",
/* 97 */	"reg: ADDU1(LOADU1(INDIRU1(addr)),LOADU1(INDIRU1(addr)))",
/* 98 */	"reg: ADDI1(reg,reg)",
/* 99 */	"reg: ADDU1(reg,reg)",
/* 100 */	"reg: ADDI1(reg,INDIRI1(addr))",
/* 101 */	"reg: ADDU1(reg,INDIRU1(addr))",
/* 102 */	"reg: ADDI1(reg,INDIRU1(addr))",
/* 103 */	"reg: ADDI1(reg,conN)",
/* 104 */	"reg: ADDU1(reg,conN)",
/* 105 */	"reg: SUBI1(INDIRI1(addr),INDIRI1(addr))",
/* 106 */	"reg: SUBU1(INDIRU1(addr),INDIRU1(addr))",
/* 107 */	"reg: SUBI1(INDIRU1(addr),INDIRU1(addr))",
/* 108 */	"reg: SUBI1(LOADI1(INDIRU1(addr)),LOADI1(INDIRU1(addr)))",
/* 109 */	"reg: SUBU1(LOADU1(INDIRU1(addr)),LOADU1(INDIRU1(addr)))",
/* 110 */	"reg: SUBI1(reg,reg)",
/* 111 */	"reg: SUBU1(reg,reg)",
/* 112 */	"reg: SUBI1(reg,INDIRI1(addr))",
/* 113 */	"reg: SUBU1(reg,INDIRU1(addr))",
/* 114 */	"reg: SUBI1(reg,INDIRU1(addr))",
/* 115 */	"reg: SUBI1(reg,conN)",
/* 116 */	"reg: SUBU1(reg,conN)",
/* 117 */	"reg: NEGI1(reg)",
/* 118 */	"reg: ADDI2(INDIRI2(faddr),con2)",
/* 119 */	"reg: ADDU2(INDIRU2(faddr),con2)",
/* 120 */	"reg: ADDP2(INDIRP2(faddr),con2)",
/* 121 */	"reg: ADDI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 122 */	"reg: ADDU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 123 */	"reg: ADDP2(INDIRP2(faddr),INDIRI2(faddr))",
/* 124 */	"reg: ADDI2(INDIRI2(addr),con2)",
/* 125 */	"reg: ADDU2(INDIRU2(addr),con2)",
/* 126 */	"reg: ADDI2(INDIRI2(addr),INDIRI2(addr))",
/* 127 */	"reg: ADDU2(INDIRU2(addr),INDIRU2(addr))",
/* 128 */	"reg: ADDI2(reg,INDIRI2(addr))",
/* 129 */	"reg: ADDU2(reg,INDIRU2(addr))",
/* 130 */	"reg: ADDI2(reg,INDIRI2(faddr))",
/* 131 */	"reg: ADDU2(reg,INDIRU2(faddr))",
/* 132 */	"reg: ADDP2(reg,INDIRP2(faddr))",
/* 133 */	"reg: ADDI2(reg,con2)",
/* 134 */	"reg: ADDU2(reg,con2)",
/* 135 */	"reg: ADDI2(reg,reg)",
/* 136 */	"reg: ADDU2(reg,reg)",
/* 137 */	"reg: ADDP2(reg,reg)",
/* 138 */	"addr: ADDP2(addr,reg)",
/* 139 */	"reg: SUBI2(INDIRI2(faddr),con2)",
/* 140 */	"reg: SUBU2(INDIRU2(faddr),con2)",
/* 141 */	"reg: SUBI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 142 */	"reg: SUBU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 143 */	"reg: SUBI2(INDIRI2(addr),con2)",
/* 144 */	"reg: SUBU2(INDIRU2(addr),con2)",
/* 145 */	"reg: SUBI2(INDIRI2(addr),INDIRI2(addr))",
/* 146 */	"reg: SUBU2(INDIRU2(addr),INDIRU2(addr))",
/* 147 */	"reg: SUBI2(reg,INDIRI2(addr))",
/* 148 */	"reg: SUBU2(reg,INDIRU2(addr))",
/* 149 */	"reg: SUBI2(reg,INDIRI2(faddr))",
/* 150 */	"reg: SUBU2(reg,INDIRU2(faddr))",
/* 151 */	"reg: SUBI2(reg,con2)",
/* 152 */	"reg: SUBU2(reg,con2)",
/* 153 */	"reg: SUBI2(reg,reg)",
/* 154 */	"reg: SUBU2(reg,reg)",
/* 155 */	"reg: NEGI2(reg)",
/* 156 */	"reg: ADDI4(reg,reg)",
/* 157 */	"reg: ADDU4(reg,reg)",
/* 158 */	"reg: SUBI4(reg,reg)",
/* 159 */	"reg: SUBU4(reg,reg)",
/* 160 */	"reg: MULI1(reg,reg)",
/* 161 */	"reg: MULU1(reg,reg)",
/* 162 */	"reg: MULI2(reg,reg)",
/* 163 */	"reg: MULU2(reg,reg)",
/* 164 */	"reg: DIVI1(reg,reg)",
/* 165 */	"reg: DIVU1(reg,reg)",
/* 166 */	"reg: DIVI2(reg,reg)",
/* 167 */	"reg: DIVU2(reg,reg)",
/* 168 */	"reg: DIVI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 169 */	"reg: DIVU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 170 */	"reg: DIVI2(reg,INDIRI2(faddr))",
/* 171 */	"reg: DIVU2(reg,INDIRU2(faddr))",
/* 172 */	"reg: MODI1(reg,reg)",
/* 173 */	"reg: MODU1(reg,reg)",
/* 174 */	"reg: MODI2(reg,reg)",
/* 175 */	"reg: MODU2(reg,reg)",
/* 176 */	"reg: MODI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 177 */	"reg: MODU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 178 */	"reg: MODI2(reg,INDIRI2(faddr))",
/* 179 */	"reg: MODU2(reg,INDIRU2(faddr))",
/* 180 */	"reg: BANDI1(INDIRI1(addr),INDIRI1(addr))",
/* 181 */	"reg: BANDU1(INDIRU1(addr),INDIRU1(addr))",
/* 182 */	"reg: BANDI1(reg,reg)",
/* 183 */	"reg: BANDU1(reg,reg)",
/* 184 */	"reg: BANDI1(reg,INDIRI1(addr))",
/* 185 */	"reg: BANDU1(reg,INDIRU1(addr))",
/* 186 */	"reg: BORI1(INDIRI1(addr),INDIRI1(addr))",
/* 187 */	"reg: BORU1(INDIRU1(addr),INDIRU1(addr))",
/* 188 */	"reg: BORI1(reg,reg)",
/* 189 */	"reg: BORU1(reg,reg)",
/* 190 */	"reg: BORI1(reg,INDIRI1(addr))",
/* 191 */	"reg: BORU1(reg,INDIRU1(addr))",
/* 192 */	"reg: BXORI1(INDIRI1(addr),INDIRI1(addr))",
/* 193 */	"reg: BXORU1(INDIRU1(addr),INDIRU1(addr))",
/* 194 */	"reg: BXORI1(reg,reg)",
/* 195 */	"reg: BXORU1(reg,reg)",
/* 196 */	"reg: BXORI1(reg,INDIRI1(addr))",
/* 197 */	"reg: BXORU1(reg,INDIRU1(addr))",
/* 198 */	"reg: BCOMI1(reg)",
/* 199 */	"reg: BCOMU1(reg)",
/* 200 */	"reg: BANDI2(reg,reg)",
/* 201 */	"reg: BANDU2(reg,reg)",
/* 202 */	"reg: BANDI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 203 */	"reg: BANDU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 204 */	"reg: BANDI2(reg,INDIRI2(faddr))",
/* 205 */	"reg: BANDU2(reg,INDIRU2(faddr))",
/* 206 */	"reg: BANDI2(INDIRI2(addr),INDIRI2(addr))",
/* 207 */	"reg: BANDU2(INDIRU2(addr),INDIRU2(addr))",
/* 208 */	"reg: BANDI2(reg,con2)",
/* 209 */	"reg: BANDU2(reg,con2)",
/* 210 */	"reg: BANDI2(INDIRI2(faddr),con2)",
/* 211 */	"reg: BANDU2(INDIRU2(faddr),con2)",
/* 212 */	"reg: BANDI2(reg,INDIRI2(addr))",
/* 213 */	"reg: BANDU2(reg,INDIRU2(addr))",
/* 214 */	"reg: BORI2(reg,reg)",
/* 215 */	"reg: BORU2(reg,reg)",
/* 216 */	"reg: BORI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 217 */	"reg: BORU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 218 */	"reg: BORI2(reg,INDIRI2(faddr))",
/* 219 */	"reg: BORU2(reg,INDIRU2(faddr))",
/* 220 */	"reg: BORI2(INDIRI2(addr),INDIRI2(addr))",
/* 221 */	"reg: BORU2(INDIRU2(addr),INDIRU2(addr))",
/* 222 */	"reg: BORI2(reg,con2)",
/* 223 */	"reg: BORU2(reg,con2)",
/* 224 */	"reg: BORI2(INDIRI2(faddr),con2)",
/* 225 */	"reg: BORU2(INDIRU2(faddr),con2)",
/* 226 */	"reg: BORI2(reg,INDIRI2(addr))",
/* 227 */	"reg: BORU2(reg,INDIRU2(addr))",
/* 228 */	"reg: BXORI2(reg,reg)",
/* 229 */	"reg: BXORU2(reg,reg)",
/* 230 */	"reg: BXORI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 231 */	"reg: BXORU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 232 */	"reg: BXORI2(reg,INDIRI2(faddr))",
/* 233 */	"reg: BXORU2(reg,INDIRU2(faddr))",
/* 234 */	"reg: BXORI2(INDIRI2(addr),INDIRI2(addr))",
/* 235 */	"reg: BXORU2(INDIRU2(addr),INDIRU2(addr))",
/* 236 */	"reg: BXORI2(reg,con2)",
/* 237 */	"reg: BXORU2(reg,con2)",
/* 238 */	"reg: BXORI2(INDIRI2(faddr),con2)",
/* 239 */	"reg: BXORU2(INDIRU2(faddr),con2)",
/* 240 */	"reg: BXORI2(reg,INDIRI2(addr))",
/* 241 */	"reg: BXORU2(reg,INDIRU2(addr))",
/* 242 */	"reg: BCOMI2(reg)",
/* 243 */	"reg: BCOMU2(reg)",
/* 244 */	"reg: LSHI2(reg,conN)",
/* 245 */	"reg: LSHU2(reg,conN)",
/* 246 */	"reg: RSHU2(reg,conN)",
/* 247 */	"reg: RSHI2(reg,conN)",
/* 248 */	"reg: LSHI2(reg,reg)",
/* 249 */	"reg: LSHU2(reg,reg)",
/* 250 */	"reg: RSHU2(reg,reg)",
/* 251 */	"reg: RSHI2(reg,reg)",
/* 252 */	"reg: LSHI1(reg,conN)",
/* 253 */	"reg: LSHU1(reg,conN)",
/* 254 */	"reg: RSHU1(reg,conN)",
/* 255 */	"reg: RSHI1(reg,conN)",
/* 256 */	"reg: LSHI1(reg,reg)",
/* 257 */	"reg: LSHU1(reg,reg)",
/* 258 */	"reg: RSHU1(reg,reg)",
/* 259 */	"reg: RSHI1(reg,reg)",
/* 260 */	"reg: CVII1(reg)",
/* 261 */	"reg: CVIU1(reg)",
/* 262 */	"reg: CVUI1(reg)",
/* 263 */	"reg: CVUU1(reg)",
/* 264 */	"reg: CVII2(reg)",
/* 265 */	"reg: CVIU2(reg)",
/* 266 */	"reg: CVUI2(reg)",
/* 267 */	"reg: CVUU2(reg)",
/* 268 */	"reg: CVII1(INDIRI2(addr))",
/* 269 */	"reg: CVUU1(INDIRU2(addr))",
/* 270 */	"reg: CVPU2(reg)",
/* 271 */	"reg: CVUP2(reg)",
/* 272 */	"reg: CVII4(reg)",
/* 273 */	"reg: CVIU4(reg)",
/* 274 */	"reg: CVUI4(reg)",
/* 275 */	"reg: CVUU4(reg)",
/* 276 */	"reg: CVPU4(reg)",
/* 277 */	"reg: CVUP4(reg)",
/* 278 */	"stmt: LABELV",
/* 279 */	"stmt: JUMPV(addr)",
/* 280 */	"stmt: JUMPV(reg)",
/* 281 */	"stmt: EQI1(reg,reg)",
/* 282 */	"stmt: EQU1(reg,reg)",
/* 283 */	"stmt: EQI1(reg,INDIRI1(addr))",
/* 284 */	"stmt: EQU1(reg,INDIRU1(addr))",
/* 285 */	"stmt: NEI1(reg,reg)",
/* 286 */	"stmt: NEU1(reg,reg)",
/* 287 */	"stmt: NEI1(reg,INDIRI1(addr))",
/* 288 */	"stmt: NEU1(reg,INDIRU1(addr))",
/* 289 */	"stmt: LTI1(reg,reg)",
/* 290 */	"stmt: LTI1(reg,INDIRI1(addr))",
/* 291 */	"stmt: LTU1(reg,reg)",
/* 292 */	"stmt: LTU1(reg,INDIRU1(addr))",
/* 293 */	"stmt: LEI1(reg,reg)",
/* 294 */	"stmt: LEI1(reg,INDIRI1(addr))",
/* 295 */	"stmt: LEU1(reg,reg)",
/* 296 */	"stmt: LEU1(reg,INDIRU1(addr))",
/* 297 */	"stmt: GTI1(reg,reg)",
/* 298 */	"stmt: GTI1(reg,INDIRI1(addr))",
/* 299 */	"stmt: GTU1(reg,reg)",
/* 300 */	"stmt: GTU1(reg,INDIRU1(addr))",
/* 301 */	"stmt: GEI1(reg,reg)",
/* 302 */	"stmt: GEI1(reg,INDIRI1(addr))",
/* 303 */	"stmt: GEU1(reg,reg)",
/* 304 */	"stmt: GEU1(reg,INDIRU1(addr))",
/* 305 */	"stmt: EQI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 306 */	"stmt: EQU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 307 */	"stmt: EQI2(reg,INDIRI2(faddr))",
/* 308 */	"stmt: EQU2(reg,INDIRU2(faddr))",
/* 309 */	"stmt: EQI2(reg,reg)",
/* 310 */	"stmt: EQU2(reg,reg)",
/* 311 */	"stmt: NEI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 312 */	"stmt: NEU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 313 */	"stmt: NEI2(reg,INDIRI2(faddr))",
/* 314 */	"stmt: NEU2(reg,INDIRU2(faddr))",
/* 315 */	"stmt: NEI2(reg,reg)",
/* 316 */	"stmt: NEU2(reg,reg)",
/* 317 */	"stmt: LTI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 318 */	"stmt: LTU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 319 */	"stmt: LTI2(reg,INDIRI2(faddr))",
/* 320 */	"stmt: LTU2(reg,INDIRU2(faddr))",
/* 321 */	"stmt: LTI2(reg,reg)",
/* 322 */	"stmt: LTU2(reg,reg)",
/* 323 */	"stmt: LEI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 324 */	"stmt: LEU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 325 */	"stmt: LEI2(reg,INDIRI2(faddr))",
/* 326 */	"stmt: LEU2(reg,INDIRU2(faddr))",
/* 327 */	"stmt: LEI2(reg,reg)",
/* 328 */	"stmt: LEU2(reg,reg)",
/* 329 */	"stmt: GTI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 330 */	"stmt: GTU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 331 */	"stmt: GTI2(reg,INDIRI2(faddr))",
/* 332 */	"stmt: GTU2(reg,INDIRU2(faddr))",
/* 333 */	"stmt: GTI2(reg,reg)",
/* 334 */	"stmt: GTU2(reg,reg)",
/* 335 */	"stmt: GEI2(INDIRI2(faddr),INDIRI2(faddr))",
/* 336 */	"stmt: GEU2(INDIRU2(faddr),INDIRU2(faddr))",
/* 337 */	"stmt: GEI2(reg,INDIRI2(faddr))",
/* 338 */	"stmt: GEU2(reg,INDIRU2(faddr))",
/* 339 */	"stmt: GEI2(reg,reg)",
/* 340 */	"stmt: GEU2(reg,reg)",
/* 341 */	"stmt: LEI2(INDIRI2(faddr),con2)",
/* 342 */	"stmt: LEU2(INDIRU2(faddr),con2)",
/* 343 */	"stmt: LEI2(reg,con2)",
/* 344 */	"stmt: LEU2(reg,con2)",
/* 345 */	"stmt: GTI2(INDIRI2(faddr),con2)",
/* 346 */	"stmt: GTU2(INDIRU2(faddr),con2)",
/* 347 */	"stmt: GTI2(reg,con2)",
/* 348 */	"stmt: GTU2(reg,con2)",
/* 349 */	"stmt: GEI2(INDIRI2(faddr),con2)",
/* 350 */	"stmt: GEU2(INDIRU2(faddr),con2)",
/* 351 */	"stmt: GEI2(reg,con2)",
/* 352 */	"stmt: GEU2(reg,con2)",
/* 353 */	"stmt: LTI2(INDIRI2(faddr),con2)",
/* 354 */	"stmt: LTU2(INDIRU2(faddr),con2)",
/* 355 */	"stmt: LTI2(reg,con2)",
/* 356 */	"stmt: LTU2(reg,con2)",
/* 357 */	"stmt: EQI2(INDIRI2(faddr),con2)",
/* 358 */	"stmt: EQU2(INDIRU2(faddr),con2)",
/* 359 */	"stmt: EQI2(reg,con2)",
/* 360 */	"stmt: EQU2(reg,con2)",
/* 361 */	"stmt: NEI2(INDIRI2(faddr),con2)",
/* 362 */	"stmt: NEU2(INDIRU2(faddr),con2)",
/* 363 */	"stmt: NEI2(reg,con2)",
/* 364 */	"stmt: NEU2(reg,con2)",
/* 365 */	"stmt: ARGI1(reg)",
/* 366 */	"stmt: ARGU1(reg)",
/* 367 */	"stmt: ARGI2(reg)",
/* 368 */	"stmt: ARGU2(reg)",
/* 369 */	"stmt: ARGP2(reg)",
/* 370 */	"stmt: ARGI4(reg)",
/* 371 */	"stmt: ARGU4(reg)",
/* 372 */	"stmt: ARGP4(reg)",
/* 373 */	"reg: CALLI1(addr)",
/* 374 */	"reg: CALLU1(addr)",
/* 375 */	"reg: CALLI2(addr)",
/* 376 */	"reg: CALLU2(addr)",
/* 377 */	"reg: CALLP2(addr)",
/* 378 */	"reg: CALLI4(addr)",
/* 379 */	"reg: CALLU4(addr)",
/* 380 */	"reg: CALLP4(addr)",
/* 381 */	"stmt: CALLV(addr)",
/* 382 */	"stmt: RETI1(reg)",
/* 383 */	"stmt: RETU1(reg)",
/* 384 */	"stmt: RETI2(reg)",
/* 385 */	"stmt: RETU2(reg)",
/* 386 */	"stmt: RETP2(reg)",
/* 387 */	"stmt: RETI4(reg)",
/* 388 */	"stmt: RETU4(reg)",
/* 389 */	"stmt: RETP4(reg)",
/* 390 */	"stmt: RETV",
/* 391 */	"reg: LOADI1(reg)",
/* 392 */	"reg: LOADU1(reg)",
/* 393 */	"reg: LOADI2(reg)",
/* 394 */	"reg: LOADU2(reg)",
/* 395 */	"reg: LOADP2(reg)",
/* 396 */	"reg: LOADI4(reg)",
/* 397 */	"reg: LOADU4(reg)",
/* 398 */	"reg: LOADP4(reg)",
/* 399 */	"stmt: reg",
};

static short _decode_stmt[] = {
	0,
	24,
	25,
	26,
	27,
	28,
	29,
	30,
	31,
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
	79,
	80,
	87,
	88,
	89,
	90,
	91,
	92,
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
	329,
	330,
	331,
	332,
	333,
	334,
	335,
	336,
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
	347,
	348,
	349,
	350,
	351,
	352,
	353,
	354,
	355,
	356,
	357,
	358,
	359,
	360,
	361,
	362,
	363,
	364,
	365,
	366,
	367,
	368,
	369,
	370,
	371,
	372,
	381,
	382,
	383,
	384,
	385,
	386,
	387,
	388,
	389,
	390,
	399,
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
	16,
	17,
	18,
	19,
	20,
	21,
	22,
	23,
	42,
	43,
	44,
	52,
	53,
	54,
	55,
	56,
	57,
	58,
	59,
	65,
	66,
	67,
	68,
	69,
	70,
	71,
	72,
	81,
	82,
	83,
	84,
	85,
	86,
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
	130,
	131,
	132,
	133,
	134,
	135,
	136,
	137,
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
	373,
	374,
	375,
	376,
	377,
	378,
	379,
	380,
	391,
	392,
	393,
	394,
	395,
	396,
	397,
	398,
};

static short _decode_con2[] = {
	0,
	34,
	35,
	36,
};

static short _decode_con1[] = {
	0,
	32,
	33,
};

static short _decode_con4[] = {
	0,
	37,
	38,
	39,
};

static short _decode_conN[] = {
	0,
	40,
	41,
};

static short _decode_addr[] = {
	0,
	45,
	46,
	51,
	138,
};

static short _decode_faddr[] = {
	0,
	47,
	48,
	49,
	50,
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
		p->rule._reg = 25;
		_closure_reg(a, c + 1);
	}
}

static void _closure_con1(NODEPTR_TYPE a, int c) {
	struct _state *p = STATE_LABEL(a);
	if (c + 1 < p->cost[_reg_NT]) {
		p->cost[_reg_NT] = c + 1;
		p->rule._reg = 24;
		_closure_reg(a, c + 1);
	}
}

static void _closure_con4(NODEPTR_TYPE a, int c) {
	struct _state *p = STATE_LABEL(a);
	if (c + 3 < p->cost[_reg_NT]) {
		p->cost[_reg_NT] = c + 3;
		p->rule._reg = 26;
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
			p->rule._reg = 30;
			_closure_reg(a, c + 0);
		}
		/* reg: INDIRI1(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 2;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 35;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: INDIRI1(ADDI2(addr,reg)) */
			LEFT_CHILD(a)->op == 2357 /* ADDI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(LEFT_CHILD(a))->x.state))->cost[_reg_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 43;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: INDIRI1(ADDP2(addr,reg)) */
			LEFT_CHILD(a)->op == 2359 /* ADDP2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(LEFT_CHILD(a))->x.state))->cost[_reg_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 45;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: INDIRI1(ADDP2(reg,addr)) */
			LEFT_CHILD(a)->op == 2359 /* ADDP2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 47;
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
			p->rule._reg = 31;
			_closure_reg(a, c + 0);
		}
		/* reg: INDIRU1(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 2;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 36;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: INDIRU1(ADDI2(addr,reg)) */
			LEFT_CHILD(a)->op == 2357 /* ADDI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(LEFT_CHILD(a))->x.state))->cost[_reg_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 44;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: INDIRU1(ADDP2(addr,reg)) */
			LEFT_CHILD(a)->op == 2359 /* ADDP2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(LEFT_CHILD(a))->x.state))->cost[_reg_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 46;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: INDIRU1(ADDP2(reg,addr)) */
			LEFT_CHILD(a)->op == 2359 /* ADDP2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 48;
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
			p->rule._reg = 215;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: CVII1(INDIRI2(addr)) */
			LEFT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 223;
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
			p->rule._reg = 216;
			_closure_reg(a, c + 0);
		}
		break;
	case 1205: /* CVUI1 */
		_label(LEFT_CHILD(a));
		/* reg: CVUI1(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 217;
			_closure_reg(a, c + 0);
		}
		break;
	case 1206: /* CVUU1 */
		_label(LEFT_CHILD(a));
		/* reg: CVUU1(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 218;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: CVUU1(INDIRU2(addr)) */
			LEFT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 224;
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
			p->rule._reg = 73;
			_closure_reg(a, c + 0);
		}
		break;
	case 1237: /* CALLI1 */
		_label(LEFT_CHILD(a));
		/* reg: CALLI1(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 5;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 233;
			_closure_reg(a, c + 0);
		}
		break;
	case 1238: /* CALLU1 */
		_label(LEFT_CHILD(a));
		/* reg: CALLU1(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 5;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 234;
			_closure_reg(a, c + 0);
		}
		break;
	case 1253: /* LOADI1 */
		_label(LEFT_CHILD(a));
		/* reg: LOADI1(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + (move(a));
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 241;
			_closure_reg(a, c + 0);
		}
		break;
	case 1254: /* LOADU1 */
		_label(LEFT_CHILD(a));
		/* reg: LOADU1(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + (move(a));
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 242;
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
				p->rule._reg = 49;
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
				p->rule._reg = 51;
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
				p->rule._reg = 52;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: ADDI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 54;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: ADDI1(reg,INDIRI1(addr)) */
			RIGHT_CHILD(a)->op == 1093 /* INDIRI1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 56;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDI1(reg,INDIRU1(addr)) */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 58;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: ADDI1(reg,conN) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_conN_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 59;
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
				p->rule._reg = 50;
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
				p->rule._reg = 53;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: ADDU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 55;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: ADDU1(reg,INDIRU1(addr)) */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 57;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: ADDU1(reg,conN) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_conN_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 60;
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
				p->rule._reg = 61;
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
				p->rule._reg = 63;
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
				p->rule._reg = 64;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: SUBI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 66;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: SUBI1(reg,INDIRI1(addr)) */
			RIGHT_CHILD(a)->op == 1093 /* INDIRI1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 68;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: SUBI1(reg,INDIRU1(addr)) */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 70;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: SUBI1(reg,conN) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_conN_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 71;
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
				p->rule._reg = 62;
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
				p->rule._reg = 65;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: SUBU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 67;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: SUBU1(reg,INDIRU1(addr)) */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 69;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: SUBU1(reg,conN) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_conN_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 72;
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
			p->rule._reg = 207;
			_closure_reg(a, c + 0);
		}
		/* reg: LSHI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 15;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 211;
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
			p->rule._reg = 208;
			_closure_reg(a, c + 0);
		}
		/* reg: LSHU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 15;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 212;
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
			p->rule._reg = 127;
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
			p->rule._reg = 128;
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
			p->rule._reg = 210;
			_closure_reg(a, c + 0);
		}
		/* reg: RSHI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 15;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 214;
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
			p->rule._reg = 209;
			_closure_reg(a, c + 0);
		}
		/* reg: RSHU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 15;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 213;
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
				p->rule._reg = 135;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BANDI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 137;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BANDI1(reg,INDIRI1(addr)) */
			RIGHT_CHILD(a)->op == 1093 /* INDIRI1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 139;
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
				p->rule._reg = 136;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BANDU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 138;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BANDU1(reg,INDIRU1(addr)) */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 140;
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
			p->rule._reg = 153;
			_closure_reg(a, c + 0);
		}
		break;
	case 1430: /* BCOMU1 */
		_label(LEFT_CHILD(a));
		/* reg: BCOMU1(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 154;
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
				p->rule._reg = 141;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BORI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 143;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BORI1(reg,INDIRI1(addr)) */
			RIGHT_CHILD(a)->op == 1093 /* INDIRI1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 145;
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
				p->rule._reg = 142;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BORU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 144;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BORU1(reg,INDIRU1(addr)) */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 146;
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
				p->rule._reg = 147;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BXORI1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 149;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BXORI1(reg,INDIRI1(addr)) */
			RIGHT_CHILD(a)->op == 1093 /* INDIRI1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 151;
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
				p->rule._reg = 148;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BXORU1(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 10;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 150;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BXORU1(reg,INDIRU1(addr)) */
			RIGHT_CHILD(a)->op == 1094 /* INDIRU1 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 1;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 152;
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
			p->rule._reg = 119;
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
			p->rule._reg = 120;
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
			p->rule._reg = 115;
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
			p->rule._reg = 116;
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
			p->rule._reg = 32;
			_closure_reg(a, c + 0);
		}
		/* reg: INDIRI2(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 2;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 37;
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
			p->rule._reg = 33;
			_closure_reg(a, c + 0);
		}
		/* reg: INDIRU2(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 2;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 38;
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
			p->rule._reg = 34;
			_closure_reg(a, c + 0);
		}
		/* reg: INDIRP2(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 2;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 39;
			_closure_reg(a, c + 0);
		}
		break;
	case 2181: /* CVII2 */
		_label(LEFT_CHILD(a));
		/* reg: CVII2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 219;
			_closure_reg(a, c + 0);
		}
		break;
	case 2182: /* CVIU2 */
		_label(LEFT_CHILD(a));
		/* reg: CVIU2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 220;
			_closure_reg(a, c + 0);
		}
		break;
	case 2198: /* CVPU2 */
		_label(LEFT_CHILD(a));
		/* reg: CVPU2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 225;
			_closure_reg(a, c + 0);
		}
		break;
	case 2229: /* CVUI2 */
		_label(LEFT_CHILD(a));
		/* reg: CVUI2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 221;
			_closure_reg(a, c + 0);
		}
		break;
	case 2230: /* CVUU2 */
		_label(LEFT_CHILD(a));
		/* reg: CVUU2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 222;
			_closure_reg(a, c + 0);
		}
		break;
	case 2231: /* CVUP2 */
		_label(LEFT_CHILD(a));
		/* reg: CVUP2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 226;
			_closure_reg(a, c + 0);
		}
		break;
	case 2245: /* NEGI2 */
		_label(LEFT_CHILD(a));
		/* reg: NEGI2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 110;
			_closure_reg(a, c + 0);
		}
		break;
	case 2261: /* CALLI2 */
		_label(LEFT_CHILD(a));
		/* reg: CALLI2(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 5;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 235;
			_closure_reg(a, c + 0);
		}
		break;
	case 2262: /* CALLU2 */
		_label(LEFT_CHILD(a));
		/* reg: CALLU2(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 5;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 236;
			_closure_reg(a, c + 0);
		}
		break;
	case 2263: /* CALLP2 */
		_label(LEFT_CHILD(a));
		/* reg: CALLP2(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 5;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 237;
			_closure_reg(a, c + 0);
		}
		break;
	case 2277: /* LOADI2 */
		_label(LEFT_CHILD(a));
		/* reg: LOADI2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + (move(a));
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 243;
			_closure_reg(a, c + 0);
		}
		break;
	case 2278: /* LOADU2 */
		_label(LEFT_CHILD(a));
		/* reg: LOADU2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + (move(a));
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 244;
			_closure_reg(a, c + 0);
		}
		break;
	case 2279: /* LOADP2 */
		_label(LEFT_CHILD(a));
		/* reg: LOADP2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + (move(a));
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 245;
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
			p->rule._reg = 27;
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
			p->rule._reg = 28;
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
			p->rule._reg = 29;
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
				p->rule._reg = 74;
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
				p->rule._reg = 77;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDI2(INDIRI2(addr),con2) */
			LEFT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 80;
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
				p->rule._reg = 82;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDI2(reg,INDIRI2(addr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 84;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDI2(reg,INDIRI2(faddr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 86;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: ADDI2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 89;
			_closure_reg(a, c + 0);
		}
		/* reg: ADDI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 8;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 91;
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
				p->rule._reg = 75;
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
				p->rule._reg = 78;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDU2(INDIRU2(addr),con2) */
			LEFT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 81;
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
				p->rule._reg = 83;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDU2(reg,INDIRU2(addr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 85;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDU2(reg,INDIRU2(faddr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 87;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: ADDU2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 90;
			_closure_reg(a, c + 0);
		}
		/* reg: ADDU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 8;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 92;
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
				p->rule._reg = 76;
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
				p->rule._reg = 79;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: ADDP2(reg,INDIRP2(faddr)) */
			RIGHT_CHILD(a)->op == 2119 /* INDIRP2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 88;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: ADDP2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 8;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 93;
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
		if (	/* reg: SUBI2(INDIRI2(VREGP),INDIRI2(VREGP)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			LEFT_CHILD(LEFT_CHILD(a))->op == 711 && /* VREGP */
			RIGHT_CHILD(a)->op == 2117 && /* INDIRI2 */
			LEFT_CHILD(RIGHT_CHILD(a))->op == 711 /* VREGP */
		) {
			c = 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 16;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: SUBI2(INDIRI2(faddr),con2) */
			LEFT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 94;
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
				p->rule._reg = 96;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: SUBI2(INDIRI2(addr),con2) */
			LEFT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 98;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: SUBI2(INDIRI2(addr),INDIRI2(addr)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 100;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: SUBI2(reg,INDIRI2(addr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 5;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 102;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: SUBI2(reg,INDIRI2(faddr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 5;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 104;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: SUBI2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 4;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 106;
			_closure_reg(a, c + 0);
		}
		/* reg: SUBI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 8;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 108;
			_closure_reg(a, c + 0);
		}
		break;
	case 2374: /* SUBU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: SUBU2(INDIRU2(VREGP),INDIRU2(VREGP)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			LEFT_CHILD(LEFT_CHILD(a))->op == 711 && /* VREGP */
			RIGHT_CHILD(a)->op == 2118 && /* INDIRU2 */
			LEFT_CHILD(RIGHT_CHILD(a))->op == 711 /* VREGP */
		) {
			c = 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 17;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: SUBU2(INDIRU2(faddr),con2) */
			LEFT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 95;
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
				p->rule._reg = 97;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: SUBU2(INDIRU2(addr),con2) */
			LEFT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 99;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: SUBU2(INDIRU2(addr),INDIRU2(addr)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 101;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: SUBU2(reg,INDIRU2(addr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 5;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 103;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: SUBU2(reg,INDIRU2(faddr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 5;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 105;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: SUBU2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 4;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 107;
			_closure_reg(a, c + 0);
		}
		/* reg: SUBU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 8;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 109;
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
			p->rule._reg = 199;
			_closure_reg(a, c + 0);
		}
		/* reg: LSHI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 15;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 203;
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
			p->rule._reg = 200;
			_closure_reg(a, c + 0);
		}
		/* reg: LSHU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 15;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 204;
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
			p->rule._reg = 129;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: MODI2(INDIRI2(faddr),INDIRI2(faddr)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 131;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: MODI2(reg,INDIRI2(faddr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 5;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 133;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 2406: /* MODU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: MODU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 130;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: MODU2(INDIRU2(faddr),INDIRU2(faddr)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 132;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: MODU2(reg,INDIRU2(faddr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 5;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 134;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 2421: /* RSHI2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: RSHI2(reg,conN) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_conN_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 202;
			_closure_reg(a, c + 0);
		}
		/* reg: RSHI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 15;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 206;
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
			p->rule._reg = 201;
			_closure_reg(a, c + 0);
		}
		/* reg: RSHU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 15;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 205;
			_closure_reg(a, c + 0);
		}
		break;
	case 2437: /* BANDI2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: BANDI2(INDIRI2(VREGP),INDIRI2(VREGP)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			LEFT_CHILD(LEFT_CHILD(a))->op == 711 && /* VREGP */
			RIGHT_CHILD(a)->op == 2117 && /* INDIRI2 */
			LEFT_CHILD(RIGHT_CHILD(a))->op == 711 /* VREGP */
		) {
			c = 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 20;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BANDI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 8;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 155;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BANDI2(INDIRI2(faddr),INDIRI2(faddr)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 157;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BANDI2(reg,INDIRI2(faddr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 159;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BANDI2(INDIRI2(addr),INDIRI2(addr)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 161;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BANDI2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 163;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BANDI2(INDIRI2(faddr),con2) */
			LEFT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 165;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BANDI2(reg,INDIRI2(addr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 167;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 2438: /* BANDU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: BANDU2(INDIRU2(VREGP),INDIRU2(VREGP)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			LEFT_CHILD(LEFT_CHILD(a))->op == 711 && /* VREGP */
			RIGHT_CHILD(a)->op == 2118 && /* INDIRU2 */
			LEFT_CHILD(RIGHT_CHILD(a))->op == 711 /* VREGP */
		) {
			c = 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 21;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BANDU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 8;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 156;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BANDU2(INDIRU2(faddr),INDIRU2(faddr)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 158;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BANDU2(reg,INDIRU2(faddr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 160;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BANDU2(INDIRU2(addr),INDIRU2(addr)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 162;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BANDU2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 164;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BANDU2(INDIRU2(faddr),con2) */
			LEFT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 166;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BANDU2(reg,INDIRU2(addr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 168;
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
			p->rule._reg = 197;
			_closure_reg(a, c + 0);
		}
		break;
	case 2454: /* BCOMU2 */
		_label(LEFT_CHILD(a));
		/* reg: BCOMU2(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 1;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 198;
			_closure_reg(a, c + 0);
		}
		break;
	case 2469: /* BORI2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: BORI2(INDIRI2(VREGP),INDIRI2(VREGP)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			LEFT_CHILD(LEFT_CHILD(a))->op == 711 && /* VREGP */
			RIGHT_CHILD(a)->op == 2117 && /* INDIRI2 */
			LEFT_CHILD(RIGHT_CHILD(a))->op == 711 /* VREGP */
		) {
			c = 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 22;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BORI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 8;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 169;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BORI2(INDIRI2(faddr),INDIRI2(faddr)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 171;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BORI2(reg,INDIRI2(faddr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 173;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BORI2(INDIRI2(addr),INDIRI2(addr)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 175;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BORI2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 177;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BORI2(INDIRI2(faddr),con2) */
			LEFT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 179;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BORI2(reg,INDIRI2(addr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 181;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 2470: /* BORU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: BORU2(INDIRU2(VREGP),INDIRU2(VREGP)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			LEFT_CHILD(LEFT_CHILD(a))->op == 711 && /* VREGP */
			RIGHT_CHILD(a)->op == 2118 && /* INDIRU2 */
			LEFT_CHILD(RIGHT_CHILD(a))->op == 711 /* VREGP */
		) {
			c = 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 23;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BORU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 8;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 170;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BORU2(INDIRU2(faddr),INDIRU2(faddr)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 172;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BORU2(reg,INDIRU2(faddr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 174;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BORU2(INDIRU2(addr),INDIRU2(addr)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 176;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BORU2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 178;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BORU2(INDIRU2(faddr),con2) */
			LEFT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 180;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BORU2(reg,INDIRU2(addr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 182;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 2485: /* BXORI2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: BXORI2(INDIRI2(VREGP),INDIRI2(VREGP)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			LEFT_CHILD(LEFT_CHILD(a))->op == 711 && /* VREGP */
			RIGHT_CHILD(a)->op == 2117 && /* INDIRI2 */
			LEFT_CHILD(RIGHT_CHILD(a))->op == 711 /* VREGP */
		) {
			c = 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 18;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BXORI2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 8;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 183;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BXORI2(INDIRI2(faddr),INDIRI2(faddr)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 185;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BXORI2(reg,INDIRI2(faddr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 187;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BXORI2(INDIRI2(addr),INDIRI2(addr)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 189;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BXORI2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 191;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BXORI2(INDIRI2(faddr),con2) */
			LEFT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 193;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BXORI2(reg,INDIRI2(addr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 195;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 2486: /* BXORU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		if (	/* reg: BXORU2(INDIRU2(VREGP),INDIRU2(VREGP)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			LEFT_CHILD(LEFT_CHILD(a))->op == 711 && /* VREGP */
			RIGHT_CHILD(a)->op == 2118 && /* INDIRU2 */
			LEFT_CHILD(RIGHT_CHILD(a))->op == 711 /* VREGP */
		) {
			c = 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 19;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BXORU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 8;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 184;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BXORU2(INDIRU2(faddr),INDIRU2(faddr)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 2;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 186;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BXORU2(reg,INDIRU2(faddr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 188;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BXORU2(INDIRU2(addr),INDIRU2(addr)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_addr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 190;
				_closure_reg(a, c + 0);
			}
		}
		/* reg: BXORU2(reg,con2) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 192;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: BXORU2(INDIRU2(faddr),con2) */
			LEFT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_con2_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 194;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: BXORU2(reg,INDIRU2(addr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_addr_NT] + 3;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 196;
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
			p->rule._reg = 121;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: DIVI2(INDIRI2(faddr),INDIRI2(faddr)) */
			LEFT_CHILD(a)->op == 2117 && /* INDIRI2 */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 123;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: DIVI2(reg,INDIRI2(faddr)) */
			RIGHT_CHILD(a)->op == 2117 /* INDIRI2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 5;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 125;
				_closure_reg(a, c + 0);
			}
		}
		break;
	case 2502: /* DIVU2 */
		_label(LEFT_CHILD(a));
		_label(RIGHT_CHILD(a));
		/* reg: DIVU2(reg,reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(RIGHT_CHILD(a)->x.state))->cost[_reg_NT] + 3;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 122;
			_closure_reg(a, c + 0);
		}
		if (	/* reg: DIVU2(INDIRU2(faddr),INDIRU2(faddr)) */
			LEFT_CHILD(a)->op == 2118 && /* INDIRU2 */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(LEFT_CHILD(a))->x.state))->cost[_faddr_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 4;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 124;
				_closure_reg(a, c + 0);
			}
		}
		if (	/* reg: DIVU2(reg,INDIRU2(faddr)) */
			RIGHT_CHILD(a)->op == 2118 /* INDIRU2 */
		) {
			c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + ((struct _state *)(LEFT_CHILD(RIGHT_CHILD(a))->x.state))->cost[_faddr_NT] + 5;
			if (c + 0 < p->cost[_reg_NT]) {
				p->cost[_reg_NT] = c + 0;
				p->rule._reg = 126;
				_closure_reg(a, c + 0);
			}
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
			p->rule._reg = 117;
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
			p->rule._reg = 118;
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
			p->rule._reg = 40;
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
			p->rule._reg = 41;
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
			p->rule._reg = 42;
			_closure_reg(a, c + 0);
		}
		break;
	case 4229: /* CVII4 */
		_label(LEFT_CHILD(a));
		/* reg: CVII4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 8;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 227;
			_closure_reg(a, c + 0);
		}
		break;
	case 4230: /* CVIU4 */
		_label(LEFT_CHILD(a));
		/* reg: CVIU4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 2;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 228;
			_closure_reg(a, c + 0);
		}
		break;
	case 4246: /* CVPU4 */
		_label(LEFT_CHILD(a));
		/* reg: CVPU4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 2;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 231;
			_closure_reg(a, c + 0);
		}
		break;
	case 4277: /* CVUI4 */
		_label(LEFT_CHILD(a));
		/* reg: CVUI4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 2;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 229;
			_closure_reg(a, c + 0);
		}
		break;
	case 4278: /* CVUU4 */
		_label(LEFT_CHILD(a));
		/* reg: CVUU4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 2;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 230;
			_closure_reg(a, c + 0);
		}
		break;
	case 4279: /* CVUP4 */
		_label(LEFT_CHILD(a));
		/* reg: CVUP4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + 0;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 232;
			_closure_reg(a, c + 0);
		}
		break;
	case 4309: /* CALLI4 */
		_label(LEFT_CHILD(a));
		/* reg: CALLI4(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 8;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 238;
			_closure_reg(a, c + 0);
		}
		break;
	case 4310: /* CALLU4 */
		_label(LEFT_CHILD(a));
		/* reg: CALLU4(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 8;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 239;
			_closure_reg(a, c + 0);
		}
		break;
	case 4311: /* CALLP4 */
		_label(LEFT_CHILD(a));
		/* reg: CALLP4(addr) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_addr_NT] + 8;
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 240;
			_closure_reg(a, c + 0);
		}
		break;
	case 4325: /* LOADI4 */
		_label(LEFT_CHILD(a));
		/* reg: LOADI4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + (move(a));
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 246;
			_closure_reg(a, c + 0);
		}
		break;
	case 4326: /* LOADU4 */
		_label(LEFT_CHILD(a));
		/* reg: LOADU4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + (move(a));
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 247;
			_closure_reg(a, c + 0);
		}
		break;
	case 4327: /* LOADP4 */
		_label(LEFT_CHILD(a));
		/* reg: LOADP4(reg) */
		c = ((struct _state *)(LEFT_CHILD(a)->x.state))->cost[_reg_NT] + (move(a));
		if (c + 0 < p->cost[_reg_NT]) {
			p->cost[_reg_NT] = c + 0;
			p->rule._reg = 248;
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
			p->rule._reg = 111;
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
			p->rule._reg = 112;
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
			p->rule._reg = 113;
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
			p->rule._reg = 114;
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
	case 390: /* stmt: RETV */
	case 278: /* stmt: LABELV */
	case 54: /* reg: ADDRLP2 */
	case 53: /* reg: ADDRFP2 */
	case 52: /* reg: ADDRGP2 */
	case 50: /* faddr: ADDRLP4 */
	case 49: /* faddr: ADDRFP4 */
	case 48: /* faddr: ADDRLP2 */
	case 47: /* faddr: ADDRFP2 */
	case 46: /* addr: ADDRGP4 */
	case 45: /* addr: ADDRGP2 */
	case 41: /* conN: CNSTU1 */
	case 40: /* conN: CNSTI1 */
	case 39: /* con4: CNSTP4 */
	case 38: /* con4: CNSTU4 */
	case 37: /* con4: CNSTI4 */
	case 36: /* con2: CNSTP2 */
	case 35: /* con2: CNSTU2 */
	case 34: /* con2: CNSTI2 */
	case 33: /* con1: CNSTU1 */
	case 32: /* con1: CNSTI1 */
	case 23: /* reg: BORU2(INDIRU2(VREGP),INDIRU2(VREGP)) */
	case 22: /* reg: BORI2(INDIRI2(VREGP),INDIRI2(VREGP)) */
	case 21: /* reg: BANDU2(INDIRU2(VREGP),INDIRU2(VREGP)) */
	case 20: /* reg: BANDI2(INDIRI2(VREGP),INDIRI2(VREGP)) */
	case 19: /* reg: BXORU2(INDIRU2(VREGP),INDIRU2(VREGP)) */
	case 18: /* reg: BXORI2(INDIRI2(VREGP),INDIRI2(VREGP)) */
	case 17: /* reg: SUBU2(INDIRU2(VREGP),INDIRU2(VREGP)) */
	case 16: /* reg: SUBI2(INDIRI2(VREGP),INDIRI2(VREGP)) */
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
	case 31: /* stmt: ASGNP4(VREGP,reg) */
	case 30: /* stmt: ASGNU4(VREGP,reg) */
	case 29: /* stmt: ASGNI4(VREGP,reg) */
	case 28: /* stmt: ASGNP2(VREGP,reg) */
	case 27: /* stmt: ASGNU2(VREGP,reg) */
	case 26: /* stmt: ASGNI2(VREGP,reg) */
	case 25: /* stmt: ASGNU1(VREGP,reg) */
	case 24: /* stmt: ASGNI1(VREGP,reg) */
	case 13: /* reg: ADDU2(INDIRU2(VREGP),con2) */
	case 12: /* reg: ADDI2(INDIRI2(VREGP),con2) */
		kids[0] = RIGHT_CHILD(p);
		break;
	case 399: /* stmt: reg */
	case 51: /* addr: faddr */
	case 44: /* reg: con4 */
	case 43: /* reg: con2 */
	case 42: /* reg: con1 */
		kids[0] = p;
		break;
	case 398: /* reg: LOADP4(reg) */
	case 397: /* reg: LOADU4(reg) */
	case 396: /* reg: LOADI4(reg) */
	case 395: /* reg: LOADP2(reg) */
	case 394: /* reg: LOADU2(reg) */
	case 393: /* reg: LOADI2(reg) */
	case 392: /* reg: LOADU1(reg) */
	case 391: /* reg: LOADI1(reg) */
	case 389: /* stmt: RETP4(reg) */
	case 388: /* stmt: RETU4(reg) */
	case 387: /* stmt: RETI4(reg) */
	case 386: /* stmt: RETP2(reg) */
	case 385: /* stmt: RETU2(reg) */
	case 384: /* stmt: RETI2(reg) */
	case 383: /* stmt: RETU1(reg) */
	case 382: /* stmt: RETI1(reg) */
	case 381: /* stmt: CALLV(addr) */
	case 380: /* reg: CALLP4(addr) */
	case 379: /* reg: CALLU4(addr) */
	case 378: /* reg: CALLI4(addr) */
	case 377: /* reg: CALLP2(addr) */
	case 376: /* reg: CALLU2(addr) */
	case 375: /* reg: CALLI2(addr) */
	case 374: /* reg: CALLU1(addr) */
	case 373: /* reg: CALLI1(addr) */
	case 372: /* stmt: ARGP4(reg) */
	case 371: /* stmt: ARGU4(reg) */
	case 370: /* stmt: ARGI4(reg) */
	case 369: /* stmt: ARGP2(reg) */
	case 368: /* stmt: ARGU2(reg) */
	case 367: /* stmt: ARGI2(reg) */
	case 366: /* stmt: ARGU1(reg) */
	case 365: /* stmt: ARGI1(reg) */
	case 280: /* stmt: JUMPV(reg) */
	case 279: /* stmt: JUMPV(addr) */
	case 277: /* reg: CVUP4(reg) */
	case 276: /* reg: CVPU4(reg) */
	case 275: /* reg: CVUU4(reg) */
	case 274: /* reg: CVUI4(reg) */
	case 273: /* reg: CVIU4(reg) */
	case 272: /* reg: CVII4(reg) */
	case 271: /* reg: CVUP2(reg) */
	case 270: /* reg: CVPU2(reg) */
	case 267: /* reg: CVUU2(reg) */
	case 266: /* reg: CVUI2(reg) */
	case 265: /* reg: CVIU2(reg) */
	case 264: /* reg: CVII2(reg) */
	case 263: /* reg: CVUU1(reg) */
	case 262: /* reg: CVUI1(reg) */
	case 261: /* reg: CVIU1(reg) */
	case 260: /* reg: CVII1(reg) */
	case 243: /* reg: BCOMU2(reg) */
	case 242: /* reg: BCOMI2(reg) */
	case 199: /* reg: BCOMU1(reg) */
	case 198: /* reg: BCOMI1(reg) */
	case 155: /* reg: NEGI2(reg) */
	case 117: /* reg: NEGI1(reg) */
	case 72: /* reg: INDIRP4(addr) */
	case 71: /* reg: INDIRU4(addr) */
	case 70: /* reg: INDIRI4(addr) */
	case 69: /* reg: INDIRP2(addr) */
	case 68: /* reg: INDIRU2(addr) */
	case 67: /* reg: INDIRI2(addr) */
	case 66: /* reg: INDIRU1(addr) */
	case 65: /* reg: INDIRI1(addr) */
	case 59: /* reg: INDIRP2(faddr) */
	case 58: /* reg: INDIRU2(faddr) */
	case 57: /* reg: INDIRI2(faddr) */
	case 56: /* reg: INDIRU1(faddr) */
	case 55: /* reg: INDIRI1(faddr) */
		kids[0] = LEFT_CHILD(p);
		break;
	case 364: /* stmt: NEU2(reg,con2) */
	case 363: /* stmt: NEI2(reg,con2) */
	case 360: /* stmt: EQU2(reg,con2) */
	case 359: /* stmt: EQI2(reg,con2) */
	case 356: /* stmt: LTU2(reg,con2) */
	case 355: /* stmt: LTI2(reg,con2) */
	case 352: /* stmt: GEU2(reg,con2) */
	case 351: /* stmt: GEI2(reg,con2) */
	case 348: /* stmt: GTU2(reg,con2) */
	case 347: /* stmt: GTI2(reg,con2) */
	case 344: /* stmt: LEU2(reg,con2) */
	case 343: /* stmt: LEI2(reg,con2) */
	case 340: /* stmt: GEU2(reg,reg) */
	case 339: /* stmt: GEI2(reg,reg) */
	case 334: /* stmt: GTU2(reg,reg) */
	case 333: /* stmt: GTI2(reg,reg) */
	case 328: /* stmt: LEU2(reg,reg) */
	case 327: /* stmt: LEI2(reg,reg) */
	case 322: /* stmt: LTU2(reg,reg) */
	case 321: /* stmt: LTI2(reg,reg) */
	case 316: /* stmt: NEU2(reg,reg) */
	case 315: /* stmt: NEI2(reg,reg) */
	case 310: /* stmt: EQU2(reg,reg) */
	case 309: /* stmt: EQI2(reg,reg) */
	case 303: /* stmt: GEU1(reg,reg) */
	case 301: /* stmt: GEI1(reg,reg) */
	case 299: /* stmt: GTU1(reg,reg) */
	case 297: /* stmt: GTI1(reg,reg) */
	case 295: /* stmt: LEU1(reg,reg) */
	case 293: /* stmt: LEI1(reg,reg) */
	case 291: /* stmt: LTU1(reg,reg) */
	case 289: /* stmt: LTI1(reg,reg) */
	case 286: /* stmt: NEU1(reg,reg) */
	case 285: /* stmt: NEI1(reg,reg) */
	case 282: /* stmt: EQU1(reg,reg) */
	case 281: /* stmt: EQI1(reg,reg) */
	case 259: /* reg: RSHI1(reg,reg) */
	case 258: /* reg: RSHU1(reg,reg) */
	case 257: /* reg: LSHU1(reg,reg) */
	case 256: /* reg: LSHI1(reg,reg) */
	case 255: /* reg: RSHI1(reg,conN) */
	case 254: /* reg: RSHU1(reg,conN) */
	case 253: /* reg: LSHU1(reg,conN) */
	case 252: /* reg: LSHI1(reg,conN) */
	case 251: /* reg: RSHI2(reg,reg) */
	case 250: /* reg: RSHU2(reg,reg) */
	case 249: /* reg: LSHU2(reg,reg) */
	case 248: /* reg: LSHI2(reg,reg) */
	case 247: /* reg: RSHI2(reg,conN) */
	case 246: /* reg: RSHU2(reg,conN) */
	case 245: /* reg: LSHU2(reg,conN) */
	case 244: /* reg: LSHI2(reg,conN) */
	case 237: /* reg: BXORU2(reg,con2) */
	case 236: /* reg: BXORI2(reg,con2) */
	case 229: /* reg: BXORU2(reg,reg) */
	case 228: /* reg: BXORI2(reg,reg) */
	case 223: /* reg: BORU2(reg,con2) */
	case 222: /* reg: BORI2(reg,con2) */
	case 215: /* reg: BORU2(reg,reg) */
	case 214: /* reg: BORI2(reg,reg) */
	case 209: /* reg: BANDU2(reg,con2) */
	case 208: /* reg: BANDI2(reg,con2) */
	case 201: /* reg: BANDU2(reg,reg) */
	case 200: /* reg: BANDI2(reg,reg) */
	case 195: /* reg: BXORU1(reg,reg) */
	case 194: /* reg: BXORI1(reg,reg) */
	case 189: /* reg: BORU1(reg,reg) */
	case 188: /* reg: BORI1(reg,reg) */
	case 183: /* reg: BANDU1(reg,reg) */
	case 182: /* reg: BANDI1(reg,reg) */
	case 175: /* reg: MODU2(reg,reg) */
	case 174: /* reg: MODI2(reg,reg) */
	case 173: /* reg: MODU1(reg,reg) */
	case 172: /* reg: MODI1(reg,reg) */
	case 167: /* reg: DIVU2(reg,reg) */
	case 166: /* reg: DIVI2(reg,reg) */
	case 165: /* reg: DIVU1(reg,reg) */
	case 164: /* reg: DIVI1(reg,reg) */
	case 163: /* reg: MULU2(reg,reg) */
	case 162: /* reg: MULI2(reg,reg) */
	case 161: /* reg: MULU1(reg,reg) */
	case 160: /* reg: MULI1(reg,reg) */
	case 159: /* reg: SUBU4(reg,reg) */
	case 158: /* reg: SUBI4(reg,reg) */
	case 157: /* reg: ADDU4(reg,reg) */
	case 156: /* reg: ADDI4(reg,reg) */
	case 154: /* reg: SUBU2(reg,reg) */
	case 153: /* reg: SUBI2(reg,reg) */
	case 152: /* reg: SUBU2(reg,con2) */
	case 151: /* reg: SUBI2(reg,con2) */
	case 138: /* addr: ADDP2(addr,reg) */
	case 137: /* reg: ADDP2(reg,reg) */
	case 136: /* reg: ADDU2(reg,reg) */
	case 135: /* reg: ADDI2(reg,reg) */
	case 134: /* reg: ADDU2(reg,con2) */
	case 133: /* reg: ADDI2(reg,con2) */
	case 116: /* reg: SUBU1(reg,conN) */
	case 115: /* reg: SUBI1(reg,conN) */
	case 111: /* reg: SUBU1(reg,reg) */
	case 110: /* reg: SUBI1(reg,reg) */
	case 104: /* reg: ADDU1(reg,conN) */
	case 103: /* reg: ADDI1(reg,conN) */
	case 99: /* reg: ADDU1(reg,reg) */
	case 98: /* reg: ADDI1(reg,reg) */
	case 80: /* stmt: ASGNP4(addr,reg) */
	case 79: /* stmt: ASGNU4(addr,reg) */
	case 78: /* stmt: ASGNI4(addr,reg) */
	case 77: /* stmt: ASGNP2(addr,reg) */
	case 76: /* stmt: ASGNU2(addr,reg) */
	case 75: /* stmt: ASGNI2(addr,reg) */
	case 74: /* stmt: ASGNU1(addr,reg) */
	case 73: /* stmt: ASGNI1(addr,reg) */
	case 64: /* stmt: ASGNP2(faddr,reg) */
	case 63: /* stmt: ASGNU2(faddr,reg) */
	case 62: /* stmt: ASGNI2(faddr,reg) */
	case 61: /* stmt: ASGNU1(faddr,reg) */
	case 60: /* stmt: ASGNI1(faddr,reg) */
		kids[0] = LEFT_CHILD(p);
		kids[1] = RIGHT_CHILD(p);
		break;
	case 86: /* reg: INDIRU1(ADDP2(reg,addr)) */
	case 85: /* reg: INDIRI1(ADDP2(reg,addr)) */
	case 84: /* reg: INDIRU1(ADDP2(addr,reg)) */
	case 83: /* reg: INDIRI1(ADDP2(addr,reg)) */
	case 82: /* reg: INDIRU1(ADDI2(addr,reg)) */
	case 81: /* reg: INDIRI1(ADDI2(addr,reg)) */
		kids[0] = LEFT_CHILD(LEFT_CHILD(p));
		kids[1] = RIGHT_CHILD(LEFT_CHILD(p));
		break;
	case 92: /* stmt: ASGNU1(ADDP2(reg,addr),reg) */
	case 91: /* stmt: ASGNI1(ADDP2(reg,addr),reg) */
	case 90: /* stmt: ASGNU1(ADDP2(addr,reg),reg) */
	case 89: /* stmt: ASGNI1(ADDP2(addr,reg),reg) */
	case 88: /* stmt: ASGNU1(ADDI2(addr,reg),reg) */
	case 87: /* stmt: ASGNI1(ADDI2(addr,reg),reg) */
		kids[0] = LEFT_CHILD(LEFT_CHILD(p));
		kids[1] = RIGHT_CHILD(LEFT_CHILD(p));
		kids[2] = RIGHT_CHILD(p);
		break;
	case 336: /* stmt: GEU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 335: /* stmt: GEI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 330: /* stmt: GTU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 329: /* stmt: GTI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 324: /* stmt: LEU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 323: /* stmt: LEI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 318: /* stmt: LTU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 317: /* stmt: LTI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 312: /* stmt: NEU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 311: /* stmt: NEI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 306: /* stmt: EQU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 305: /* stmt: EQI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 235: /* reg: BXORU2(INDIRU2(addr),INDIRU2(addr)) */
	case 234: /* reg: BXORI2(INDIRI2(addr),INDIRI2(addr)) */
	case 231: /* reg: BXORU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 230: /* reg: BXORI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 221: /* reg: BORU2(INDIRU2(addr),INDIRU2(addr)) */
	case 220: /* reg: BORI2(INDIRI2(addr),INDIRI2(addr)) */
	case 217: /* reg: BORU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 216: /* reg: BORI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 207: /* reg: BANDU2(INDIRU2(addr),INDIRU2(addr)) */
	case 206: /* reg: BANDI2(INDIRI2(addr),INDIRI2(addr)) */
	case 203: /* reg: BANDU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 202: /* reg: BANDI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 193: /* reg: BXORU1(INDIRU1(addr),INDIRU1(addr)) */
	case 192: /* reg: BXORI1(INDIRI1(addr),INDIRI1(addr)) */
	case 187: /* reg: BORU1(INDIRU1(addr),INDIRU1(addr)) */
	case 186: /* reg: BORI1(INDIRI1(addr),INDIRI1(addr)) */
	case 181: /* reg: BANDU1(INDIRU1(addr),INDIRU1(addr)) */
	case 180: /* reg: BANDI1(INDIRI1(addr),INDIRI1(addr)) */
	case 177: /* reg: MODU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 176: /* reg: MODI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 169: /* reg: DIVU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 168: /* reg: DIVI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 146: /* reg: SUBU2(INDIRU2(addr),INDIRU2(addr)) */
	case 145: /* reg: SUBI2(INDIRI2(addr),INDIRI2(addr)) */
	case 142: /* reg: SUBU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 141: /* reg: SUBI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 127: /* reg: ADDU2(INDIRU2(addr),INDIRU2(addr)) */
	case 126: /* reg: ADDI2(INDIRI2(addr),INDIRI2(addr)) */
	case 123: /* reg: ADDP2(INDIRP2(faddr),INDIRI2(faddr)) */
	case 122: /* reg: ADDU2(INDIRU2(faddr),INDIRU2(faddr)) */
	case 121: /* reg: ADDI2(INDIRI2(faddr),INDIRI2(faddr)) */
	case 107: /* reg: SUBI1(INDIRU1(addr),INDIRU1(addr)) */
	case 106: /* reg: SUBU1(INDIRU1(addr),INDIRU1(addr)) */
	case 105: /* reg: SUBI1(INDIRI1(addr),INDIRI1(addr)) */
	case 95: /* reg: ADDI1(INDIRU1(addr),INDIRU1(addr)) */
	case 94: /* reg: ADDU1(INDIRU1(addr),INDIRU1(addr)) */
	case 93: /* reg: ADDI1(INDIRI1(addr),INDIRI1(addr)) */
		kids[0] = LEFT_CHILD(LEFT_CHILD(p));
		kids[1] = LEFT_CHILD(RIGHT_CHILD(p));
		break;
	case 109: /* reg: SUBU1(LOADU1(INDIRU1(addr)),LOADU1(INDIRU1(addr))) */
	case 108: /* reg: SUBI1(LOADI1(INDIRU1(addr)),LOADI1(INDIRU1(addr))) */
	case 97: /* reg: ADDU1(LOADU1(INDIRU1(addr)),LOADU1(INDIRU1(addr))) */
	case 96: /* reg: ADDI1(LOADI1(INDIRU1(addr)),LOADI1(INDIRU1(addr))) */
		kids[0] = LEFT_CHILD(LEFT_CHILD(LEFT_CHILD(p)));
		kids[1] = LEFT_CHILD(LEFT_CHILD(RIGHT_CHILD(p)));
		break;
	case 338: /* stmt: GEU2(reg,INDIRU2(faddr)) */
	case 337: /* stmt: GEI2(reg,INDIRI2(faddr)) */
	case 332: /* stmt: GTU2(reg,INDIRU2(faddr)) */
	case 331: /* stmt: GTI2(reg,INDIRI2(faddr)) */
	case 326: /* stmt: LEU2(reg,INDIRU2(faddr)) */
	case 325: /* stmt: LEI2(reg,INDIRI2(faddr)) */
	case 320: /* stmt: LTU2(reg,INDIRU2(faddr)) */
	case 319: /* stmt: LTI2(reg,INDIRI2(faddr)) */
	case 314: /* stmt: NEU2(reg,INDIRU2(faddr)) */
	case 313: /* stmt: NEI2(reg,INDIRI2(faddr)) */
	case 308: /* stmt: EQU2(reg,INDIRU2(faddr)) */
	case 307: /* stmt: EQI2(reg,INDIRI2(faddr)) */
	case 304: /* stmt: GEU1(reg,INDIRU1(addr)) */
	case 302: /* stmt: GEI1(reg,INDIRI1(addr)) */
	case 300: /* stmt: GTU1(reg,INDIRU1(addr)) */
	case 298: /* stmt: GTI1(reg,INDIRI1(addr)) */
	case 296: /* stmt: LEU1(reg,INDIRU1(addr)) */
	case 294: /* stmt: LEI1(reg,INDIRI1(addr)) */
	case 292: /* stmt: LTU1(reg,INDIRU1(addr)) */
	case 290: /* stmt: LTI1(reg,INDIRI1(addr)) */
	case 288: /* stmt: NEU1(reg,INDIRU1(addr)) */
	case 287: /* stmt: NEI1(reg,INDIRI1(addr)) */
	case 284: /* stmt: EQU1(reg,INDIRU1(addr)) */
	case 283: /* stmt: EQI1(reg,INDIRI1(addr)) */
	case 241: /* reg: BXORU2(reg,INDIRU2(addr)) */
	case 240: /* reg: BXORI2(reg,INDIRI2(addr)) */
	case 233: /* reg: BXORU2(reg,INDIRU2(faddr)) */
	case 232: /* reg: BXORI2(reg,INDIRI2(faddr)) */
	case 227: /* reg: BORU2(reg,INDIRU2(addr)) */
	case 226: /* reg: BORI2(reg,INDIRI2(addr)) */
	case 219: /* reg: BORU2(reg,INDIRU2(faddr)) */
	case 218: /* reg: BORI2(reg,INDIRI2(faddr)) */
	case 213: /* reg: BANDU2(reg,INDIRU2(addr)) */
	case 212: /* reg: BANDI2(reg,INDIRI2(addr)) */
	case 205: /* reg: BANDU2(reg,INDIRU2(faddr)) */
	case 204: /* reg: BANDI2(reg,INDIRI2(faddr)) */
	case 197: /* reg: BXORU1(reg,INDIRU1(addr)) */
	case 196: /* reg: BXORI1(reg,INDIRI1(addr)) */
	case 191: /* reg: BORU1(reg,INDIRU1(addr)) */
	case 190: /* reg: BORI1(reg,INDIRI1(addr)) */
	case 185: /* reg: BANDU1(reg,INDIRU1(addr)) */
	case 184: /* reg: BANDI1(reg,INDIRI1(addr)) */
	case 179: /* reg: MODU2(reg,INDIRU2(faddr)) */
	case 178: /* reg: MODI2(reg,INDIRI2(faddr)) */
	case 171: /* reg: DIVU2(reg,INDIRU2(faddr)) */
	case 170: /* reg: DIVI2(reg,INDIRI2(faddr)) */
	case 150: /* reg: SUBU2(reg,INDIRU2(faddr)) */
	case 149: /* reg: SUBI2(reg,INDIRI2(faddr)) */
	case 148: /* reg: SUBU2(reg,INDIRU2(addr)) */
	case 147: /* reg: SUBI2(reg,INDIRI2(addr)) */
	case 132: /* reg: ADDP2(reg,INDIRP2(faddr)) */
	case 131: /* reg: ADDU2(reg,INDIRU2(faddr)) */
	case 130: /* reg: ADDI2(reg,INDIRI2(faddr)) */
	case 129: /* reg: ADDU2(reg,INDIRU2(addr)) */
	case 128: /* reg: ADDI2(reg,INDIRI2(addr)) */
	case 114: /* reg: SUBI1(reg,INDIRU1(addr)) */
	case 113: /* reg: SUBU1(reg,INDIRU1(addr)) */
	case 112: /* reg: SUBI1(reg,INDIRI1(addr)) */
	case 102: /* reg: ADDI1(reg,INDIRU1(addr)) */
	case 101: /* reg: ADDU1(reg,INDIRU1(addr)) */
	case 100: /* reg: ADDI1(reg,INDIRI1(addr)) */
		kids[0] = LEFT_CHILD(p);
		kids[1] = LEFT_CHILD(RIGHT_CHILD(p));
		break;
	case 362: /* stmt: NEU2(INDIRU2(faddr),con2) */
	case 361: /* stmt: NEI2(INDIRI2(faddr),con2) */
	case 358: /* stmt: EQU2(INDIRU2(faddr),con2) */
	case 357: /* stmt: EQI2(INDIRI2(faddr),con2) */
	case 354: /* stmt: LTU2(INDIRU2(faddr),con2) */
	case 353: /* stmt: LTI2(INDIRI2(faddr),con2) */
	case 350: /* stmt: GEU2(INDIRU2(faddr),con2) */
	case 349: /* stmt: GEI2(INDIRI2(faddr),con2) */
	case 346: /* stmt: GTU2(INDIRU2(faddr),con2) */
	case 345: /* stmt: GTI2(INDIRI2(faddr),con2) */
	case 342: /* stmt: LEU2(INDIRU2(faddr),con2) */
	case 341: /* stmt: LEI2(INDIRI2(faddr),con2) */
	case 239: /* reg: BXORU2(INDIRU2(faddr),con2) */
	case 238: /* reg: BXORI2(INDIRI2(faddr),con2) */
	case 225: /* reg: BORU2(INDIRU2(faddr),con2) */
	case 224: /* reg: BORI2(INDIRI2(faddr),con2) */
	case 211: /* reg: BANDU2(INDIRU2(faddr),con2) */
	case 210: /* reg: BANDI2(INDIRI2(faddr),con2) */
	case 144: /* reg: SUBU2(INDIRU2(addr),con2) */
	case 143: /* reg: SUBI2(INDIRI2(addr),con2) */
	case 140: /* reg: SUBU2(INDIRU2(faddr),con2) */
	case 139: /* reg: SUBI2(INDIRI2(faddr),con2) */
	case 125: /* reg: ADDU2(INDIRU2(addr),con2) */
	case 124: /* reg: ADDI2(INDIRI2(addr),con2) */
	case 120: /* reg: ADDP2(INDIRP2(faddr),con2) */
	case 119: /* reg: ADDU2(INDIRU2(faddr),con2) */
	case 118: /* reg: ADDI2(INDIRI2(faddr),con2) */
		kids[0] = LEFT_CHILD(LEFT_CHILD(p));
		kids[1] = RIGHT_CHILD(p);
		break;
	case 269: /* reg: CVUU1(INDIRU2(addr)) */
	case 268: /* reg: CVII1(INDIRI2(addr)) */
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
