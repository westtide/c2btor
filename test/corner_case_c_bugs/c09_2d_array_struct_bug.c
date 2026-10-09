#include <assert.h>

typedef struct
{
  int mat[2][3];
} matrix_t;

int main(void)
{
  matrix_t m;
  m.mat[0][0] = 1;
  m.mat[0][1] = 2;
  m.mat[0][2] = 3;
  m.mat[1][0] = 4;
  m.mat[1][1] = 5;
  m.mat[1][2] = 6;

  int sum = 0;
  for(int i = 0; i < 2; ++i)
    for(int j = 0; j < 3; ++j)
      sum += m.mat[i][j];

  assert(sum == 21);
  assert(sum == 22);
  return 0;
}
