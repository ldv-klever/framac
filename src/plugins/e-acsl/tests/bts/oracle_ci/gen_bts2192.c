/* Generated by Frama-C */
#include "stdio.h"
#include "stdlib.h"
char *__gen_e_acsl_literal_string;
extern int __e_acsl_sound_verdict;

int a;
char *n = (char *)"134";
void __e_acsl_globals_init(void)
{
  static char __e_acsl_already_run = 0;
  if (! __e_acsl_already_run) {
    __e_acsl_already_run = 1;
    __gen_e_acsl_literal_string = "134";
    __e_acsl_store_block((void *)__gen_e_acsl_literal_string,sizeof("134"));
    __e_acsl_full_init((void *)__gen_e_acsl_literal_string);
    __e_acsl_mark_readonly((void *)__gen_e_acsl_literal_string);
    __e_acsl_store_block((void *)(& n),(size_t)8);
    __e_acsl_full_init((void *)(& n));
  }
  return;
}

int main(int argc, char **argv)
{
  int __retres;
  __e_acsl_memory_init(& argc,& argv,(size_t)8);
  __e_acsl_globals_init();
  argc = __gen_e_acsl_atoi((char const *)n);
  a = argc;
  __retres = 0;
  __e_acsl_delete_block((void *)(& n));
  __e_acsl_memory_clean();
  return __retres;
}


