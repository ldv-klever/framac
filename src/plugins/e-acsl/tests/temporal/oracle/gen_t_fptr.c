/* Generated by Frama-C */
#include "stdio.h"
#include "stdlib.h"
int *foo(int *p)
{
  int *q = p;
  return q;
}

void __e_acsl_globals_init(void)
{
  __e_acsl_store_block((void *)(& foo),(size_t)1);
  __e_acsl_full_init((void *)(& foo));
  return;
}

int main(int argc, char const **argv)
{
  int __retres;
  int *q;
  __e_acsl_memory_init(& argc,(char ***)(& argv),(size_t)8);
  __e_acsl_globals_init();
  __e_acsl_store_block((void *)(& q),(size_t)8);
  int *p = & argc;
  __e_acsl_store_block((void *)(& p),(size_t)8);
  __e_acsl_full_init((void *)(& p));
  __e_acsl_temporal_store_nblock((void *)(& p),(void *)(& argc));
  int *(*fp)(int *) = & foo;
  __e_acsl_store_block((void *)(& fp),(size_t)8);
  __e_acsl_full_init((void *)(& fp));
  __e_acsl_temporal_store_nblock((void *)(& fp),(void *)(& foo));
  __e_acsl_temporal_store_nblock((void *)(& fp),(void *)(& foo));
  __e_acsl_full_init((void *)(& fp));
  fp = & foo;
  /*@ assert \valid_function(fp); */ ;
  __e_acsl_temporal_reset_parameters();
  __e_acsl_temporal_reset_return();
  __e_acsl_temporal_save_nreferent_parameter((void *)(& p),0U);
  __e_acsl_full_init((void *)(& q));
  q = (*fp)(p);
  __e_acsl_temporal_store_nblock((void *)(& q),(void *)*(& q));
  /*@ assert \valid(q); */
  {
    int __gen_e_acsl_initialized;
    int __gen_e_acsl_and;
    __gen_e_acsl_initialized = __e_acsl_initialized((void *)(& q),
                                                    sizeof(int *));
    if (__gen_e_acsl_initialized) {
      int __gen_e_acsl_valid;
      __gen_e_acsl_valid = __e_acsl_valid((void *)q,sizeof(int),(void *)q,
                                          (void *)(& q));
      __gen_e_acsl_and = __gen_e_acsl_valid;
    }
    else __gen_e_acsl_and = 0;
    __e_acsl_assert(__gen_e_acsl_and,(char *)"Assertion",(char *)"main",
                    (char *)"\\valid(q)",20);
  }
  __retres = 0;
  __e_acsl_delete_block((void *)(& argc));
  __e_acsl_delete_block((void *)(& foo));
  __e_acsl_delete_block((void *)(& fp));
  __e_acsl_delete_block((void *)(& q));
  __e_acsl_delete_block((void *)(& p));
  __e_acsl_memory_clean();
  return __retres;
}


