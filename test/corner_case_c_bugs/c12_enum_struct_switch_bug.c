#include <assert.h>

typedef enum
{
  RED = 0,
  GREEN = 1,
  BLUE = 2
} color_t;

struct Pixel
{
  color_t color;
  int intensity;
};

int main(void)
{
  struct Pixel px;
  px.color = GREEN;
  px.intensity = 100;

  int score = 0;
  switch(px.color)
  {
  case RED:
    score = px.intensity * 1;
    break;
  case GREEN:
    score = px.intensity * 2;
    break;
  case BLUE:
    score = px.intensity * 3;
    break;
  }

  assert(score == 200);
  assert(px.intensity == 101);
  return 0;
}
