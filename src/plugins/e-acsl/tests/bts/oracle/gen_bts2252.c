/* Generated by Frama-C */
#include "stdio.h"
#include "stdlib.h"
char *__gen_e_acsl_literal_string;
/*@ assigns \result, *(x_0 + (0 ..)), *(x_1 + (0 ..));
    assigns \result \from *(x_0 + (0 ..)), *(x_1 + (0 ..)), x_2;
    assigns *(x_0 + (0 ..)) \from *(x_0 + (0 ..)), *(x_1 + (0 ..)), x_2;
    assigns *(x_1 + (0 ..)) \from *(x_0 + (0 ..)), *(x_1 + (0 ..)), x_2;
 */
extern int ( /* missing proto */ strncpy)(char *x_0, char *x_1, int x_2);

void __e_acsl_globals_init(void)
{
  __gen_e_acsl_literal_string = "Test Code";
  __e_acsl_store_block((void *)__gen_e_acsl_literal_string,
                       sizeof("Test Code"));
  __e_acsl_full_init((void *)__gen_e_acsl_literal_string);
  __e_acsl_mark_readonly((void *)__gen_e_acsl_literal_string);
  return;
}

int main(void)
{
  int __retres;
  int i;
  __e_acsl_memory_init((int *)0,(char ***)0,(size_t)8);
  __e_acsl_globals_init();
  char *srcbuf = (char *)__gen_e_acsl_literal_string;
  __e_acsl_store_block((void *)(& srcbuf),(size_t)8);
  __e_acsl_full_init((void *)(& srcbuf));
  int loc = 1;
  char *destbuf = malloc((unsigned long)10 * sizeof(char));
  char ch = (char)'o';
  if (destbuf != (char *)0) {
    i = -1;
    while (i < 0) {
      /*@ assert ¬\valid_read(srcbuf + i); */
      {
        int __gen_e_acsl_valid_read;
        __gen_e_acsl_valid_read = __e_acsl_valid_read((void *)(srcbuf + i),
                                                      sizeof(char),
                                                      (void *)srcbuf,
                                                      (void *)(& srcbuf));
        __e_acsl_assert(! __gen_e_acsl_valid_read,(char *)"Assertion",
                        (char *)"main",(char *)"!\\valid_read(srcbuf + i)",
                        16);
      }
      /*@ assert Eva: mem_access: \valid_read(srcbuf + i); */
      if ((int)*(srcbuf + i) == (int)ch) loc = i;
      i ++;
    }
    strncpy(destbuf + loc,srcbuf + loc,1);
    free((void *)destbuf);
  }
  __retres = 0;
  __e_acsl_delete_block((void *)(& srcbuf));
  __e_acsl_memory_clean();
  return __retres;
}


