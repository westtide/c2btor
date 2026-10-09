// Repeated allocation requires fresh runtime identities without loop expansion.
// Reaching the configured allocation budget is a separate model_limit property.
#include <stdlib.h>

int main()
{
  int *p;
  int i = 0;
  int last_val = 0;

  while(i < 3)
  {
    p = (int *)malloc(sizeof(int));
    *p = i;
    last_val = *p;
    i++;
  }

  // On executions with successful allocations this assertion holds.
  __CPROVER_assert(last_val == 2, "last loop value");
  return 0;
}
