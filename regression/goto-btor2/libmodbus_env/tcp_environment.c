/* Explicit verification environment, not an implementation of a host OS.
 * IPv4 TCP; DNS resolution and serial devices unavailable. Syscall outcomes
 * and received bytes are nondeterministic. No real socket is opened.
 * See README.md for the abstraction boundary and API preconditions.
 */
#include "tcp_environment.h"

#include <netinet/in.h>
#include <sys/ioctl.h>
#include <sys/select.h>
#include <sys/socket.h>

#include <errno.h>
#include <limits.h>
#include <netdb.h>
#include <stdarg.h>
#include <stdlib.h>
#include <termios.h>
#include <time.h>

extern int __VERIFIER_nondet_int(void);
extern unsigned char __VERIFIER_nondet_uchar(void);
extern unsigned int __VERIFIER_nondet_uint(void);
extern unsigned long __VERIFIER_nondet_ulong(void);
extern long __VERIFIER_nondet_long(void);

static int env_error(void)
{
  errno = __VERIFIER_nondet_int();
  __CPROVER_assume(errno > 0);
  return -1;
}

static int env_status(void)
{
  return __VERIFIER_nondet_int() ? env_error() : 0;
}

static int env_fd(void)
{
  if(__VERIFIER_nondet_int())
    return env_error();
  int fd = __VERIFIER_nondet_int();
  /* This profile covers descriptor numbers representable by an fd_set. */
  __CPROVER_assume(fd >= 0 && fd < FD_SETSIZE);
  return fd;
}

int socket(int domain, int type, int protocol)
{
  return env_fd();
}
int bind(int fd, const struct sockaddr *addr, socklen_t size)
{
  return env_status();
}
int listen(int fd, int backlog)
{
  return env_status();
}
int connect(int fd, const struct sockaddr *addr, socklen_t size)
{
  return env_status();
}
int shutdown(int fd, int how)
{
  return env_status();
}
int setsockopt(int fd, int level, int name, const void *value, socklen_t size)
{
  return env_status();
}

ssize_t recv(int fd, void *buffer, size_t size, int flags)
{
  if(__VERIFIER_nondet_int())
    return env_error();
  long count = __VERIFIER_nondet_long();
  __CPROVER_assume(count >= 0 && (unsigned long)count <= size);
  for(long i = 0; i < count; ++i)
    ((unsigned char *)buffer)[i] = __VERIFIER_nondet_uchar();
  return count;
}

ssize_t send(int fd, const void *buffer, size_t size, int flags)
{
  if(__VERIFIER_nondet_int())
    return env_error();
  long count = __VERIFIER_nondet_long();
  __CPROVER_assume(count >= 0 && (unsigned long)count <= size);
  return count;
}

int accept(int fd, struct sockaddr *addr, socklen_t *size)
{
  int result = env_fd();
  if(result < 0 || addr == NULL)
    return result;
  /* Original IPv4 server passes a complete sockaddr_in object. */
  __CPROVER_assert(
    size != NULL && *size >= sizeof(struct sockaddr_in),
    "TCP environment: accept address capacity");
  struct sockaddr_in *ipv4 = (struct sockaddr_in *)addr;
  ipv4->sin_len = sizeof(struct sockaddr_in);
  ipv4->sin_family = AF_INET;
  ipv4->sin_port = (unsigned short)__VERIFIER_nondet_uint();
  ipv4->sin_addr.s_addr = __VERIFIER_nondet_uint();
  for(unsigned i = 0; i < sizeof(ipv4->sin_zero); ++i)
    ipv4->sin_zero[i] = 0;
  *size = sizeof(struct sockaddr_in);
  return result;
}

int getsockopt(int fd, int level, int name, void *value, socklen_t *size)
{
  __CPROVER_assert(
    level == SOL_SOCKET && name == SO_ERROR,
    "TCP environment: only SO_ERROR is modeled");
  if(__VERIFIER_nondet_int())
    return env_error();
  __CPROVER_assert(
    size != NULL && *size >= sizeof(int),
    "TCP environment: getsockopt output capacity");
  int error = __VERIFIER_nondet_int();
  __CPROVER_assume(error >= 0);
  *(int *)value = error;
  *size = sizeof(int);
  return 0;
}

/* Keep a nondeterministic subset of the supplied readiness bits. We deliberately
 * overapproximate the relationship between the masks and the return count. */
static void env_fd_subset(fd_set *set, int ready)
{
  if(set != NULL)
    for(unsigned i = 0; i < sizeof(set->fds_bits) / sizeof(set->fds_bits[0]);
        ++i)
      set->fds_bits[i] = ready ? set->fds_bits[i] & __VERIFIER_nondet_int() : 0;
}
int select(
  int nfds,
  fd_set *readfds,
  fd_set *writefds,
  fd_set *exceptfds,
  struct timeval *timeout)
{
  if(__VERIFIER_nondet_int())
    return env_error();
  int count = __VERIFIER_nondet_int();
  __CPROVER_assume(count >= 0 && count <= 3 * nfds);
  env_fd_subset(readfds, count);
  env_fd_subset(writefds, count);
  env_fd_subset(exceptfds, count);
  /* Darwin leaves the supplied timeout unchanged. */
  return count;
}

int __darwin_check_fd_set_overflow(int fd, const void *set, int unlimited)
{
  /* Model only valid, fixed-size fd_set accesses. Expose violations as bad. */
  __CPROVER_assert(
    fd >= 0 && fd < FD_SETSIZE, "TCP environment: descriptor fits fd_set");
  return fd >= 0 && fd < FD_SETSIZE;
}

int ioctl(int fd, unsigned long request, ...)
{
  /* The TCP path uses only FIONBIO, which does not write the supplied integer.
   * Serial requests fail in this profile and do not modify their arguments. */
  if(request == FIONBIO)
    return env_status();
  errno = ENOTTY;
  return -1;
}

int nanosleep(const struct timespec *requested, struct timespec *remaining)
{
  if(!__VERIFIER_nondet_int())
    return 0;
  int result = env_error();
  if(errno == EINTR && remaining != NULL)
  {
    long seconds = __VERIFIER_nondet_long();
    long nanos = __VERIFIER_nondet_long();
    __CPROVER_assume(seconds >= 0 && seconds <= requested->tv_sec);
    __CPROVER_assume(nanos >= 0 && nanos < 1000000000);
    __CPROVER_assume(
      seconds < requested->tv_sec || nanos <= requested->tv_nsec);
    remaining->tv_sec = seconds;
    remaining->tv_nsec = nanos;
  }
  return result;
}

/* Explicitly unavailable facilities; do not claim TCP_PI/RTU success coverage. */
int getaddrinfo(
  const char *node,
  const char *service,
  const struct addrinfo *hints,
  struct addrinfo **result)
{
  return EAI_NONAME;
}
void freeaddrinfo(struct addrinfo *result)
{
  __CPROVER_assert(
    result == NULL, "TCP environment: no successful address resolution");
}
const char *gai_strerror(int error)
{
  return "address resolution unavailable in TCP verification environment";
}
int tcgetattr(int fd, struct termios *attributes)
{
  errno = ENOTTY;
  return -1;
}
int tcsetattr(int fd, int action, const struct termios *attributes)
{
  errno = ENOTTY;
  return -1;
}
int tcflush(int fd, int selector)
{
  errno = ENOTTY;
  return -1;
}
int cfsetispeed(struct termios *attributes, speed_t speed)
{
  attributes->c_ispeed = speed;
  return 0;
}
int cfsetospeed(struct termios *attributes, speed_t speed)
{
  attributes->c_ospeed = speed;
  return 0;
}

size_t __builtin___strlcpy_chk(
  char *dst,
  const char *src,
  size_t size,
  size_t object_size)
{
  if(size > object_size)
    abort();
  size_t length = 0;
  while(src[length] != 0)
  {
    if(size > 0 && length < size - 1)
      dst[length] = src[length];
    ++length;
  }
  if(size > 0)
    dst[length < size - 1 ? length : size - 1] = 0;
  return length;
}
