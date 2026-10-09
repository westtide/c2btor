#include <netinet/in.h>
#include <sys/select.h>
#include <sys/socket.h>
int main(void)
{
  struct sockaddr_in peer;
  socklen_t length = sizeof(peer);
  int accepted = accept(3, (struct sockaddr *)&peer, &length);
  if(accepted >= 0)
    __CPROVER_assert(
      length == sizeof(peer) && peer.sin_family == AF_INET,
      "accept initializes IPv4 address");
  int error = -42;
  length = sizeof(error);
  int status = getsockopt(3, SOL_SOCKET, SO_ERROR, &error, &length);
  if(status == 0)
    __CPROVER_assert(
      error >= 0 && length == sizeof(error), "SO_ERROR is written");
  else
    __CPROVER_assert(error == -42, "failed getsockopt leaves output unchanged");
#ifdef NEGATIVE
  __CPROVER_assume(status == 0);
  __CPROVER_assert(error == -42, "negative: SO_ERROR must overwrite output");
#endif
}
