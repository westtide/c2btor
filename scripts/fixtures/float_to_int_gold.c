// Compare CBMC's bit-level conversion behavior, including inputs for which C
// does not specify a representable integer result. Do not run this fixture as a
// native C test: the reference is CBMC's float_utilst circuit, not host casts.
extern void __CPROVER_assume(_Bool);
extern void __CPROVER_assert(_Bool, const char *);

#if FLOAT_WIDTH == 32
typedef unsigned int input_bitst;
typedef float input_floatt;
extern input_bitst __VERIFIER_nondet_uint(void);
#define NONDET_BITS() __VERIFIER_nondet_uint()
#elif FLOAT_WIDTH == 64
typedef unsigned long long input_bitst;
typedef double input_floatt;
extern input_bitst __VERIFIER_nondet_ulonglong(void);
#define NONDET_BITS() __VERIFIER_nondet_ulonglong()
#else
#error FLOAT_WIDTH must be 32 or 64
#endif

int result_signed;
unsigned int result_unsigned;

int main(void)
{
  union
  {
    input_bitst bits;
    input_floatt value;
  } input;
  // Keep both conversions symbolic; ASSUME constrains the SAT input rather
  // than substituting a floating constant before circuit construction.
  input.bits = NONDET_BITS();
  __CPROVER_assume(input.bits == INPUT_BITS);
  result_signed = (int)input.value;
  result_unsigned = (unsigned int)input.value;
  // Obtain a concrete CBMC JSON trace and a corresponding BTOR2 bad frame.
  __CPROVER_assert(0, "capture float-to-integer result bits");
  return 0;
}
