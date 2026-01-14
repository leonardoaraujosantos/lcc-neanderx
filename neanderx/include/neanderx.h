/*
 * NEANDER-X Standard Header
 *
 * This header provides type definitions and macros for the
 * NEANDER-X 8-bit processor.
 */

#ifndef _NEANDERX_H
#define _NEANDERX_H

/* NEANDER-X is an 8-bit processor */
typedef unsigned char uint8_t;
typedef signed char   int8_t;
typedef unsigned int  uint16_t;  /* 2 bytes for 'long' */
typedef signed int    int16_t;

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

/* Maximum and minimum values for 16-bit types */
#define INT16_MAX   32767
#define INT16_MIN   (-32768)
#define UINT16_MAX  65535

/* Size of types */
#define CHAR_BIT    8
#define CHAR_MAX    UINT8_MAX
#define CHAR_MIN    0

#endif /* _NEANDERX_H */
