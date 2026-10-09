struct hole
{
  int pos;
};

void set_len(struct hole *h, unsigned long int new_len)
{
  h->pos = new_len;
}

int main()
{
  int i = 0;
  struct hole h;
  h.pos = 0;
  for(i = 0; i < 5; i++)
    // __CPROVER_assigns(h.pos, i)
    __CPROVER_loop_invariant(h.pos == i)
    {
      set_len(&h, h.pos + 1);
    }
}
