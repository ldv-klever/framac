/* run.config
   OPT: -val -slevel 10
*/

void *Frama_C_alloc_by_stack(unsigned long i);
void *Frama_C_alloc_size(unsigned long i);

void main(int c) {
  int x;
  int *s;
  if(c) {
    x = 1;
    s = Frama_C_alloc_by_stack(100);
  } else {
    x = 2;
    s = 0;
  }

  int *p = Frama_C_alloc_by_stack(c);
  int *q = Frama_C_alloc_by_stack(12);
  int *r = Frama_C_alloc_size(100);
  *p = 1;
  *(p+2) = 3;
  *(p+24999) = 4;

  *q = 1;
  Frama_C_show_each(q+2);
  *(q+2) = 3;

  *r = 1;
  *(r+2) = 3;

  //  *s = 1;
}
