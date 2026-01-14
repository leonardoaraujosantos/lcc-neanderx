/* NEANDER-X 8-bit processor backend driver configuration */

#include <string.h>

static char rcsid[] = "$Id: neanderx.c $";

#ifndef LCCDIR
#define LCCDIR "/usr/local/lib/lcc/"
#endif

/*
 * NEANDER-X is an educational 8-bit processor.
 * This driver configuration generates NEANDER-X assembly output.
 *
 * The output is assembly code that can be:
 * 1. Assembled by a custom NEANDER-X assembler
 * 2. Loaded into a NEANDER-X simulator
 * 3. Used for educational purposes
 *
 * Since NEANDER-X doesn't have a standard toolchain,
 * the default output is assembly (.s) files.
 */

char *suffixes[] = { ".c", ".i", ".s", ".o", ".bin", 0 };
char inputs[256] = "";

/* Preprocessor - use system cpp or lcc's cpp */
char *cpp[] = {
    LCCDIR "cpp",
    "-D__NEANDERX__",
    "-D__8BIT__",
    "-D__STDC__=1",
    "$1", "$2", "$3", 0
};

/* Include paths */
char *include[] = {
    "-I" LCCDIR "include",
    "-I" LCCDIR "neanderx/include",
    0
};

/* Compiler - target neanderx */
char *com[] = {
    LCCDIR "rcc",
    "-target=neanderx",
    "$1", "$2", "$3",
    0
};

/*
 * Assembler - NEANDER-X doesn't have a standard assembler yet.
 * This placeholder can be replaced with a custom assembler path.
 * For now, we just copy the assembly output.
 */
char *as[] = {
    "/bin/cat",  /* Placeholder - just output the assembly */
    "$1", "$2",
    0
};

/*
 * Linker - NEANDER-X doesn't have a standard linker.
 * The output is typically a raw binary or hex file for simulation.
 * This is a placeholder that can be customized.
 */
char *ld[] = {
    "/bin/cat",  /* Placeholder - just concatenate files */
    "$1", "$2",
    "-o", "$3",
    0
};

extern char *concat(char *, char *);

int option(char *arg) {
    if (strncmp(arg, "-lccdir=", 8) == 0) {
        /* Update paths when lccdir is specified */
        cpp[0] = concat(&arg[8], "/cpp");
        include[0] = concat("-I", concat(&arg[8], "/include"));
        include[1] = concat("-I", concat(&arg[8], "/neanderx/include"));
        com[0] = concat(&arg[8], "/rcc");
    } else if (strcmp(arg, "-S") == 0) {
        /* Generate assembly only (default for NEANDER-X) */
        ;
    } else if (strcmp(arg, "-g") == 0) {
        /* Debug info - add comment-style debug */
        ;
    } else if (strncmp(arg, "-asm=", 5) == 0) {
        /* Custom assembler path */
        as[0] = &arg[5];
    } else if (strncmp(arg, "-sim=", 5) == 0) {
        /* Custom simulator path for running */
        ld[0] = &arg[5];
    } else
        return 0;
    return 1;
}
