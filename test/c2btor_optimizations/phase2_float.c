extern unsigned __VERIFIER_nondet_uint(void);
static float static_float[2] = {1.5f, -0.0f};
static double static_double[2] = {1.5, -0.0};

int main(void)
{
  unsigned i = __VERIFIER_nondet_uint();
  float automatic_float[3] = {1.5f, 2.5f, -0.0f};
  double automatic_double[3] = {1.5, 2.5, -0.0};
  __CPROVER_assert(static_float[0] == 1.5f && static_double[0] == 1.5,
                  "check nonzero static float initializers");
  __CPROVER_assert(1.0f / static_float[i] < 0.0f &&
                    1.0 / static_double[i] < 0.0,
                  "check static negative-zero sign through IEEE reciprocal");
  __CPROVER_assert(automatic_float[0] == 1.5f &&
                    automatic_float[i] == 2.5f &&
                    automatic_double[0] == 1.5 &&
                    automatic_double[i] == 2.5,
                  "check automatic float initializers");
  __CPROVER_assert(1.0f / automatic_float[2] < 0.0f &&
                    1.0 / automatic_double[2] < 0.0,
                  "check automatic negative-zero sign through IEEE reciprocal");
  automatic_float[i] = 1.5f;
  automatic_double[i] = 1.5;
  __CPROVER_assert(automatic_float[i] == 1.5f &&
                    automatic_double[i] == 1.5,
                  "check first float overwrite");
  automatic_float[i] = 2.5f;
  automatic_double[i] = 2.5;
  __CPROVER_assert(automatic_float[i] == 2.5f &&
                    automatic_double[i] == 2.5,
                  "check last float overwrite");
  __CPROVER_assert(0, "optimization-reached");
}
