#include <sys/socket.h>
int main(void)
{
  unsigned char bytes[5] = {11, 22, 33, 44, 55};
  long n = recv(3, bytes + 1, 3, 0);
  __CPROVER_assert(n >= -1 && n <= 3, "recv count bounds");
  __CPROVER_assert(
    bytes[0] == 11 && bytes[4] == 55, "recv preserves outside bytes");
  if(n <= 0)
    __CPROVER_assert(
      bytes[1] == 22 && bytes[2] == 33 && bytes[3] == 44,
      "recv error and EOF preserve buffer");
  if(n == 1)
    __CPROVER_assert(
      bytes[2] == 33 && bytes[3] == 44, "recv short read suffix");
#ifdef NEGATIVE
  __CPROVER_assume(n == 3);
  __CPROVER_assert(bytes[1] == 22, "negative: received byte may change");
#endif
}
