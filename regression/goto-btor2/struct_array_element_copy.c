#include <assert.h>

struct record
{
  int key;
  int value;
};

int main(void)
{
  struct record src[3], dst[3];
  for(int i = 0; i < 3; ++i)
  {
    src[i].key = i;
    src[i].value = 10 + i;
    dst[i] = src[i];
  }
  for(int i = 0; i < 3; ++i)
  {
    assert(dst[i].key == src[i].key);
    assert(dst[i].value == src[i].value);
  }
}
