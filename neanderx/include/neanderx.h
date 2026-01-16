/*
 * NEANDER-X Standard Header - 16-bit Version
 *
 * This header provides type definitions and macros for the
 * NEANDER-X 16-bit processor.
 *
 * Type Sizes:
 * - char:    1 byte (8-bit character)
 * - short:   2 bytes (16-bit native)
 * - int:     2 bytes (16-bit native)
 * - long:    4 bytes (32-bit)
 * - pointer: 2 bytes (16-bit address space)
 */

#ifndef _NEANDERX_H
#define _NEANDERX_H

/* Fixed-width integer types for 16-bit architecture */
typedef unsigned char  uint8_t;
typedef signed char    int8_t;
typedef unsigned int   uint16_t;   /* Native 16-bit unsigned */
typedef signed int     int16_t;    /* Native 16-bit signed */
typedef unsigned long  uint32_t;   /* 32-bit unsigned */
typedef signed long    int32_t;    /* 32-bit signed */

/* Size types */
typedef unsigned int   size_t;     /* 16-bit size type */
typedef signed int     ptrdiff_t;  /* 16-bit pointer difference */

/* Boolean type */
typedef unsigned char bool;
#define true  1
#define false 0

/* NULL pointer */
#define NULL ((void*)0)

/* Port addresses for I/O */
#define IO_PORT0  0x00
#define IO_PORT1  0x01

/* Memory-mapped I/O macros */
#define INPUT()       __input(0)
#define OUTPUT(val)   __output(0, val)

/* Inline assembly helpers (not directly supported, use asm comments) */
#define NOP()         /* NOP */
#define HALT()        /* HLT */

/* Maximum and minimum values for 8-bit types */
#define INT8_MAX    127
#define INT8_MIN    (-128)
#define UINT8_MAX   255

/* Maximum and minimum values for 16-bit types (native int) */
#define INT16_MAX   32767
#define INT16_MIN   (-32768)
#define UINT16_MAX  65535U

/* Maximum and minimum values for 32-bit types (long) */
#define INT32_MAX   2147483647L
#define INT32_MIN   (-2147483647L - 1)
#define UINT32_MAX  4294967295UL

/* Standard integer limits for this architecture */
#define CHAR_BIT    8
#define CHAR_MAX    255
#define CHAR_MIN    0
#define SCHAR_MAX   127
#define SCHAR_MIN   (-128)
#define UCHAR_MAX   255

#define SHRT_MAX    32767
#define SHRT_MIN    (-32768)
#define USHRT_MAX   65535U

#define INT_MAX     32767
#define INT_MIN     (-32768)
#define UINT_MAX    65535U

#define LONG_MAX    2147483647L
#define LONG_MIN    (-2147483647L - 1)
#define ULONG_MAX   4294967295UL

/* Pointer size in bits */
#define __SIZEOF_POINTER__  2
#define __SIZEOF_INT__      2
#define __SIZEOF_LONG__     4
#define __SIZEOF_SHORT__    2

#endif /* _NEANDERX_H */
