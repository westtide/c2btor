#ifndef C2BTOR_SYMBOLIC_HEAP_FIXTURE_TYPES_H
#define C2BTOR_SYMBOLIC_HEAP_FIXTURE_TYPES_H

/* Determine width from the target parsed by CBMC, not host SDK headers. */
typedef __typeof__(sizeof(int)) size_t;
typedef __typeof__(sizeof(int)) uintptr_t;

#ifndef C2BTOR_FIXTURE_UNSIGNED_MALLOC
void *malloc(size_t size);
#endif
void free(void *ptr);

#endif
