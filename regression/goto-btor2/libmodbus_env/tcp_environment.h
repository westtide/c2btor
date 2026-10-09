#ifndef C2BTOR_LIBMODBUS_TCP_ENVIRONMENT_H
#define C2BTOR_LIBMODBUS_TCP_ENVIRONMENT_H
#include <stddef.h>
/* Declare the fortified builtin before the SDK macro expands strlcpy to it. */
size_t __builtin___strlcpy_chk(char *, const char *, size_t, size_t);
#endif
