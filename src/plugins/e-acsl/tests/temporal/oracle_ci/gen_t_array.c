/* Generated by Frama-C */
#include "stdio.h"
#include "stdlib.h"
int main(void)
{
  int __retres;
  int *src[3];
  __e_acsl_memory_init((int *)0,(char ***)0,(size_t)8);
  __e_acsl_store_block((void *)(src),(size_t)24);
  int a = 111;
  __e_acsl_store_block((void *)(& a),(size_t)4);
  __e_acsl_full_init((void *)(& a));
  int b = 222;
  __e_acsl_store_block((void *)(& b),(size_t)4);
  __e_acsl_full_init((void *)(& b));
  __e_acsl_temporal_store_nblock((void *)(src),(void *)(& a));
  __e_acsl_initialize((void *)(src),sizeof(int *));
  src[0] = & a;
  __e_acsl_temporal_store_nblock((void *)(& src[1]),(void *)(& b));
  __e_acsl_initialize((void *)(& src[1]),sizeof(int *));
  src[1] = & b;
  /*@ assert \valid(src[0]); */
  {
    int __gen_e_acsl_initialized;
    int __gen_e_acsl_and;
    __gen_e_acsl_initialized = __e_acsl_initialized((void *)(src),
                                                    sizeof(int *));
    if (__gen_e_acsl_initialized) {
      int __gen_e_acsl_valid;
      __gen_e_acsl_valid = __e_acsl_valid((void *)src[0],sizeof(int),
                                          (void *)src[0],(void *)(src));
      __gen_e_acsl_and = __gen_e_acsl_valid;
    }
    else __gen_e_acsl_and = 0;
    __e_acsl_assert(__gen_e_acsl_and,(char *)"Assertion",(char *)"main",
                    (char *)"\\valid(src[0])",13);
  }
  /*@ assert \valid(src[1]); */
  {
    int __gen_e_acsl_initialized_2;
    int __gen_e_acsl_and_2;
    __gen_e_acsl_initialized_2 = __e_acsl_initialized((void *)(& src[1]),
                                                      sizeof(int *));
    if (__gen_e_acsl_initialized_2) {
      int __gen_e_acsl_valid_2;
      __gen_e_acsl_valid_2 = __e_acsl_valid((void *)src[1],sizeof(int),
                                            (void *)src[1],
                                            (void *)(& src[1]));
      __gen_e_acsl_and_2 = __gen_e_acsl_valid_2;
    }
    else __gen_e_acsl_and_2 = 0;
    __e_acsl_assert(__gen_e_acsl_and_2,(char *)"Assertion",(char *)"main",
                    (char *)"\\valid(src[1])",14);
  }
  /*@ assert ??\valid(src[2]); */
  {
    int __gen_e_acsl_initialized_3;
    int __gen_e_acsl_and_3;
    __gen_e_acsl_initialized_3 = __e_acsl_initialized((void *)(& src[2]),
                                                      sizeof(int *));
    if (__gen_e_acsl_initialized_3) {
      int __gen_e_acsl_valid_3;
      __gen_e_acsl_valid_3 = __e_acsl_valid((void *)src[2],sizeof(int),
                                            (void *)src[2],
                                            (void *)(& src[2]));
      __gen_e_acsl_and_3 = __gen_e_acsl_valid_3;
    }
    else __gen_e_acsl_and_3 = 0;
    __e_acsl_assert(! __gen_e_acsl_and_3,(char *)"Assertion",(char *)"main",
                    (char *)"!\\valid(src[2])",15);
  }
  __retres = 0;
  __e_acsl_delete_block((void *)(src));
  __e_acsl_delete_block((void *)(& b));
  __e_acsl_delete_block((void *)(& a));
  __e_acsl_memory_clean();
  return __retres;
}


