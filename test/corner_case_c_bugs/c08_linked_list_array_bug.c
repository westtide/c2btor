#include <assert.h>

struct Node
{
  int value;
  int next_idx;
};

int main(void)
{
  struct Node nodes[3];
  nodes[0].value = 10;
  nodes[0].next_idx = 1;
  nodes[1].value = 20;
  nodes[1].next_idx = 2;
  nodes[2].value = 30;
  nodes[2].next_idx = -1;

  int sum = 0;
  int cur = 0;
  for(int i = 0; i < 3; ++i)
  {
    sum += nodes[cur].value;
    cur = nodes[cur].next_idx;
  }
  assert(sum == 60);
  assert(sum == 61);
  return 0;
}
