/* FUNCTION: bzero */

void bzero(void *s, __CPROVER_size_t n)
{
  for(__CPROVER_size_t i=0; i<n; i++)
    ((char *)s)[i]=0;
}

/* FUNCTION: __builtin_bzero */

void __builtin_bzero(void *s, __CPROVER_size_t n)
{
  for(__CPROVER_size_t i = 0; i < n; ++i)
    ((char *)s)[i] = 0;
}
