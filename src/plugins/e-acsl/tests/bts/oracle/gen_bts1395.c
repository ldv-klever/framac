/* Generated by Frama-C */
#include "stdio.h"
#include "stdlib.h"
/*@ requires n > 0; */
int __gen_e_acsl_fact(int n);

int fact(int n)
{
  int __retres;
  int tmp;
  if (n == 1) {
    __retres = 1;
    goto return_label;
  }
  tmp = __gen_e_acsl_fact(n - 1);
  ;
  __retres = n * tmp;
  return_label: return __retres;
}

int main(void)
{
  int __retres;
  __e_acsl_memory_init((int *)0,(char ***)0,(size_t)8);
  int x = __gen_e_acsl_fact(5);
  /*@ assert x ≡ 120; */
  __e_acsl_assert(x == 120,(char *)"Assertion",(char *)"main",
                  (char *)"x == 120",13);
  __retres = 0;
  return __retres;
}

/*@ requires n > 0; */
int __gen_e_acsl_fact(int n)
{
  int __retres;
  __e_acsl_assert(n > 0,(char *)"Precondition",(char *)"fact",
                  (char *)"n > 0",5);
  __retres = fact(n);
  return __retres;
}


