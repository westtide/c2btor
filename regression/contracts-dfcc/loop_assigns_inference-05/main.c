#include <stdlib.h>

#define SIZE 8

int main()
{
  int i = 0;
  int *j = malloc(SIZE * sizeof(int));
  for(i = 0; i < SIZE; i++)
    // __CPROVER_assigns(h.pos, i)
    __CPROVER_loop_invariant(0 <= i && i <= SIZE)
    {
      int *k;
      k = j + i;
      *k = 1;
    }
}
