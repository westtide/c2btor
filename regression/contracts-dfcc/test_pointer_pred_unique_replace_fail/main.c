int nondet_int();
void foo(
  int *in,
  int *in1,
  int *in2,
  int *in3,
  int *in4,
  int *in5,
  int *in6,
  int **out1,
  int **out2,
  int **out3,
  int **out4,
  int **out5,
  int **out6)
  // clang-format off
__CPROVER_requires(__CPROVER_is_fresh(in, sizeof(int)))
__CPROVER_requires(__CPROVER_is_fresh(in1, sizeof(int)) && __CPROVER_pointer_in_range_dfcc(in, in1, in))
__CPROVER_requires(__CPROVER_pointer_in_range_dfcc(in, in2, in) && __CPROVER_is_fresh(in2, sizeof(int)))
__CPROVER_requires(__CPROVER_is_fresh(in3, sizeof(int)) && __CPROVER_pointer_equals(in3, in))
__CPROVER_requires(__CPROVER_pointer_equals(in4, in) && __CPROVER_is_fresh(in4, sizeof(int)))
__CPROVER_requires(__CPROVER_pointer_in_range_dfcc(in, in5, in) && __CPROVER_pointer_equals(in5, in))
__CPROVER_requires(__CPROVER_pointer_equals(in6, in) && __CPROVER_pointer_in_range_dfcc(in, in6, in))
__CPROVER_requires(__CPROVER_is_fresh(out1, sizeof(int *)))
__CPROVER_requires(__CPROVER_is_fresh(out2, sizeof(int *)))
__CPROVER_requires(__CPROVER_is_fresh(out3, sizeof(int *)))
__CPROVER_requires(__CPROVER_is_fresh(out4, sizeof(int *)))
__CPROVER_requires(__CPROVER_is_fresh(out5, sizeof(int *)))
__CPROVER_requires(__CPROVER_is_fresh(out6, sizeof(int *)))
__CPROVER_assigns(*out1, *out2, *out3, *out4, *out5, *out6)
__CPROVER_ensures(__CPROVER_is_fresh(*out1, sizeof(int)) && __CPROVER_pointer_in_range_dfcc(in, *out1, in))
__CPROVER_ensures(__CPROVER_pointer_in_range_dfcc(in, *out2, in) && __CPROVER_is_fresh(*out2, sizeof(int)))
__CPROVER_ensures(__CPROVER_is_fresh(*out3, sizeof(int)) && __CPROVER_pointer_equals(*out3, in))
__CPROVER_ensures(__CPROVER_pointer_equals(*out4, in) && __CPROVER_is_fresh(*out4, sizeof(int)))
__CPROVER_ensures(__CPROVER_pointer_in_range_dfcc(in, *out5, in) && __CPROVER_pointer_equals(*out5, in))
__CPROVER_ensures(__CPROVER_pointer_equals(*out6, in) && __CPROVER_pointer_in_range_dfcc(in, *out6, in))
// clang-format on
{
  int *tmp1 = malloc(sizeof(int));
  __CPROVER_assume(tmp1);
  *out1 = nondet_int() ? tmp1 : in;

  int *tmp2 = malloc(sizeof(int));
  __CPROVER_assume(tmp2);
  *out2 = nondet_int() ? tmp2 : in;

  int *tmp3 = malloc(sizeof(int));
  __CPROVER_assume(tmp3);
  *out3 = nondet_int() ? tmp3 : in;

  int *tmp4 = malloc(sizeof(int));
  __CPROVER_assume(tmp4);
  *out4 = nondet_int() ? tmp4 : in;

  *out5 = in;

  *out6 = in;
}

void bar()
  // clang-format off
__CPROVER_requires(1)
__CPROVER_assigns()
__CPROVER_ensures(1)
// clang-format on
{
  int in, in1, in2, in3, in4, in5, in6;
  int *out1, *out2, *out3, *out4, *out5, *out6;
  foo(
    &in,
    nondet_bool() ? &in : &in1,
    nondet_bool() ? &in : &in2,
    nondet_bool() ? &in : &in3,
    nondet_bool() ? &in : &in4,
    &in,
    &in,
    &out1,
    &out2,
    &out3,
    &out4,
    &out5,
    &out6);
}

int main()
{
  bar();
  return 0;
}
