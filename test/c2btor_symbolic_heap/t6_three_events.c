#include "fixture_types.h"

int main(void)
{
  void *first = 0;
  void *second = 0;
  void *third = 0;
  for(int i = 0; i < 3; ++i)
  {
    void *p = malloc(8);
    if(i == 0)
      first = p;
    else if(i == 1)
      second = p;
    else
      third = p;
  }
  if(!first || !second || !third)
    return 0;
  __CPROVER_assert(
    __CPROVER_POINTER_OBJECT(first) != __CPROVER_POINTER_OBJECT(second) &&
      __CPROVER_POINTER_OBJECT(second) != __CPROVER_POINTER_OBJECT(third) &&
      __CPROVER_POINTER_OBJECT(first) != __CPROVER_POINTER_OBJECT(third),
    "T6 three executions of one malloc site retain three fresh identities");
  return 0;
}
