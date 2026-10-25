#ifndef C2BTOR_AIOB_STDLIB_H
#define C2BTOR_AIOB_STDLIB_H
/* The corresponding task selects Linux/i386 and declares unsigned size_t. */
#ifndef NULL
#define NULL ((void *)0)
#endif
typedef unsigned int size_t;
extern void *malloc(size_t);
extern void *calloc(size_t, size_t);
extern void *realloc(void *, size_t);
extern void free(void *);
extern void abort(void);
extern void exit(int);
#endif
