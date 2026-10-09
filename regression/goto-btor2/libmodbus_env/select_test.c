#include <sys/select.h>
int main(void)
{
  fd_set set = {{8}};
  struct timeval timeout = {1, 123};
  int rc = select(4, &set, 0, 0, &timeout);
  __CPROVER_assert(rc >= -1 && rc <= 12, "select return range");
  __CPROVER_assert(timeout.tv_sec == 1 && timeout.tv_usec == 123,
                  "Darwin select preserves timeout");
  if(rc == -1)
    __CPROVER_assert(set.fds_bits[0] == 8, "select failure preserves mask");
  else if(rc == 0)
    __CPROVER_assert(set.fds_bits[0] == 0, "select timeout clears mask");
  else
    __CPROVER_assert((set.fds_bits[0] & ~8) == 0, "select returns a subset");
}
