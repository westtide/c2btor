#include <assert.h>

struct node
{
  int value;
  struct node *next;
};

int main(void)
{
  struct node nodes[3];
  for(int i = 0; i < 3; ++i)
  {
    nodes[i].value = i + 1;
    nodes[i].next = i == 2 ? 0 : &nodes[i + 1];
  }

  assert(&nodes[0] != &nodes[1]);
  struct node *p = &nodes[0];
  for(int i = 0; i < 3; ++i)
  {
    assert(p == &nodes[i]);
    assert(p->value == i + 1);
    p = p->next;
  }
  assert(p == 0);
}
