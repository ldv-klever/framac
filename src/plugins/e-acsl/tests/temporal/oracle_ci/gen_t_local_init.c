/* Generated by Frama-C */
#include "stdio.h"
#include "stdlib.h"
char *__gen_e_acsl_literal_string_4;
char *__gen_e_acsl_literal_string_3;
char *__gen_e_acsl_literal_string;
char *__gen_e_acsl_literal_string_2;
char *__gen_e_acsl_literal_string_5;
char *__gen_e_acsl_literal_string_7;
char *__gen_e_acsl_literal_string_6;
struct tree_desc {
   int *extra_bits ;
};
typedef struct tree_desc tree_desc;
struct tree_desc2 {
   struct tree_desc desc ;
};
typedef struct tree_desc2 tree_desc2;
void build_tree(tree_desc *desc)
{
  int *extra;
  __e_acsl_store_block((void *)(& extra),(size_t)8);
  __e_acsl_store_block((void *)(& desc),(size_t)8);
  __e_acsl_temporal_pull_parameter((void *)(& desc),0U,8UL);
  __e_acsl_temporal_store_nreferent((void *)(& extra),
                                    (void *)(& desc->extra_bits));
  __e_acsl_full_init((void *)(& extra));
  extra = desc->extra_bits;
  /*@ assert \valid(extra); */
  {
    int __gen_e_acsl_initialized;
    int __gen_e_acsl_and;
    __gen_e_acsl_initialized = __e_acsl_initialized((void *)(& extra),
                                                    sizeof(int *));
    if (__gen_e_acsl_initialized) {
      int __gen_e_acsl_valid;
      __gen_e_acsl_valid = __e_acsl_valid((void *)extra,sizeof(int),
                                          (void *)extra,(void *)(& extra));
      __gen_e_acsl_and = __gen_e_acsl_valid;
    }
    else __gen_e_acsl_and = 0;
    __e_acsl_assert(__gen_e_acsl_and,(char *)"Assertion",
                    (char *)"build_tree",(char *)"\\valid(extra)",23);
  }
  __e_acsl_delete_block((void *)(& desc));
  __e_acsl_delete_block((void *)(& extra));
  return;
}

char *Strings[2][2] =
  {{(char *)"the", (char *)"tha"}, {(char *)"thi", (char *)"tho"}};
char *Str[4] = {(char *)"foo", (char *)"bar", (char *)"baz", (char *)0};
void __e_acsl_globals_init(void)
{
  static char __e_acsl_already_run = 0;
  if (! __e_acsl_already_run) {
    __e_acsl_already_run = 1;
    __gen_e_acsl_literal_string_4 = "tho";
    __e_acsl_store_block((void *)__gen_e_acsl_literal_string_4,sizeof("tho"));
    __e_acsl_full_init((void *)__gen_e_acsl_literal_string_4);
    __e_acsl_mark_readonly((void *)__gen_e_acsl_literal_string_4);
    __gen_e_acsl_literal_string_3 = "thi";
    __e_acsl_store_block((void *)__gen_e_acsl_literal_string_3,sizeof("thi"));
    __e_acsl_full_init((void *)__gen_e_acsl_literal_string_3);
    __e_acsl_mark_readonly((void *)__gen_e_acsl_literal_string_3);
    __gen_e_acsl_literal_string = "the";
    __e_acsl_store_block((void *)__gen_e_acsl_literal_string,sizeof("the"));
    __e_acsl_full_init((void *)__gen_e_acsl_literal_string);
    __e_acsl_mark_readonly((void *)__gen_e_acsl_literal_string);
    __gen_e_acsl_literal_string_2 = "tha";
    __e_acsl_store_block((void *)__gen_e_acsl_literal_string_2,sizeof("tha"));
    __e_acsl_full_init((void *)__gen_e_acsl_literal_string_2);
    __e_acsl_mark_readonly((void *)__gen_e_acsl_literal_string_2);
    __gen_e_acsl_literal_string_5 = "foo";
    __e_acsl_store_block((void *)__gen_e_acsl_literal_string_5,sizeof("foo"));
    __e_acsl_full_init((void *)__gen_e_acsl_literal_string_5);
    __e_acsl_mark_readonly((void *)__gen_e_acsl_literal_string_5);
    __gen_e_acsl_literal_string_7 = "baz";
    __e_acsl_store_block((void *)__gen_e_acsl_literal_string_7,sizeof("baz"));
    __e_acsl_full_init((void *)__gen_e_acsl_literal_string_7);
    __e_acsl_mark_readonly((void *)__gen_e_acsl_literal_string_7);
    __gen_e_acsl_literal_string_6 = "bar";
    __e_acsl_store_block((void *)__gen_e_acsl_literal_string_6,sizeof("bar"));
    __e_acsl_full_init((void *)__gen_e_acsl_literal_string_6);
    __e_acsl_mark_readonly((void *)__gen_e_acsl_literal_string_6);
    __e_acsl_store_block((void *)(Str),(size_t)32);
    __e_acsl_full_init((void *)(& Str));
    __e_acsl_store_block((void *)(Strings),(size_t)32);
    __e_acsl_full_init((void *)(& Strings));
    __e_acsl_temporal_store_nblock((void *)(Str),
                                   (void *)__gen_e_acsl_literal_string_5);
    __e_acsl_temporal_store_nblock((void *)(& Str[1]),
                                   (void *)__gen_e_acsl_literal_string_6);
    __e_acsl_temporal_store_nblock((void *)(& Str[2]),
                                   (void *)__gen_e_acsl_literal_string_7);
    __e_acsl_temporal_store_nblock((void *)(& Str[3]),(void *)0);
    __e_acsl_temporal_store_nblock((void *)(& Strings[0][0]),
                                   (void *)__gen_e_acsl_literal_string);
    __e_acsl_temporal_store_nblock((void *)(& Strings[0][1]),
                                   (void *)__gen_e_acsl_literal_string_2);
    __e_acsl_temporal_store_nblock((void *)(& Strings[1][0]),
                                   (void *)__gen_e_acsl_literal_string_3);
    __e_acsl_temporal_store_nblock((void *)(& Strings[1][1]),
                                   (void *)__gen_e_acsl_literal_string_4);
  }
  return;
}

int main(int argc, char const **argv)
{
  int __retres;
  __e_acsl_memory_init(& argc,(char ***)(& argv),(size_t)8);
  __e_acsl_globals_init();
  char *strings[2][2] =
    {{(char *)__gen_e_acsl_literal_string,
      (char *)__gen_e_acsl_literal_string_2},
     {(char *)__gen_e_acsl_literal_string_3,
      (char *)__gen_e_acsl_literal_string_4}};
  __e_acsl_store_block((void *)(strings),(size_t)32);
  __e_acsl_full_init((void *)(& strings));
  __e_acsl_temporal_store_nblock((void *)(& strings[1][1]),
                                 (void *)__gen_e_acsl_literal_string_4);
  __e_acsl_temporal_store_nblock((void *)(& strings[1][0]),
                                 (void *)__gen_e_acsl_literal_string_3);
  __e_acsl_temporal_store_nblock((void *)(& strings[0][1]),
                                 (void *)__gen_e_acsl_literal_string_2);
  __e_acsl_temporal_store_nblock((void *)(& strings[0][0]),
                                 (void *)__gen_e_acsl_literal_string);
  char **p = (char **)(strings);
  __e_acsl_store_block((void *)(& p),(size_t)8);
  __e_acsl_full_init((void *)(& p));
  __e_acsl_temporal_store_nblock((void *)(& p),(void *)(strings));
  /*@ assert \valid_read(p); */
  {
    int __gen_e_acsl_initialized;
    int __gen_e_acsl_and;
    __gen_e_acsl_initialized = __e_acsl_initialized((void *)(& p),
                                                    sizeof(char **));
    if (__gen_e_acsl_initialized) {
      int __gen_e_acsl_valid_read;
      __gen_e_acsl_valid_read = __e_acsl_valid_read((void *)p,sizeof(char *),
                                                    (void *)p,(void *)(& p));
      __gen_e_acsl_and = __gen_e_acsl_valid_read;
    }
    else __gen_e_acsl_and = 0;
    __e_acsl_assert(__gen_e_acsl_and,(char *)"Assertion",(char *)"main",
                    (char *)"\\valid_read(p)",41);
  }
  /*@ assert \valid_read(*p); */
  {
    int __gen_e_acsl_initialized_2;
    int __gen_e_acsl_and_3;
    __gen_e_acsl_initialized_2 = __e_acsl_initialized((void *)p,
                                                      sizeof(char *));
    if (__gen_e_acsl_initialized_2) {
      int __gen_e_acsl_initialized_3;
      int __gen_e_acsl_and_2;
      int __gen_e_acsl_valid_read_3;
      __gen_e_acsl_initialized_3 = __e_acsl_initialized((void *)(& p),
                                                        sizeof(char **));
      if (__gen_e_acsl_initialized_3) {
        int __gen_e_acsl_valid_read_2;
        __gen_e_acsl_valid_read_2 = __e_acsl_valid_read((void *)p,
                                                        sizeof(char *),
                                                        (void *)p,
                                                        (void *)(& p));
        __gen_e_acsl_and_2 = __gen_e_acsl_valid_read_2;
      }
      else __gen_e_acsl_and_2 = 0;
      __e_acsl_assert(__gen_e_acsl_and_2,(char *)"RTE",(char *)"main",
                      (char *)"mem_access: \\valid_read(p)",42);
      __gen_e_acsl_valid_read_3 = __e_acsl_valid_read((void *)*p,
                                                      sizeof(char),
                                                      (void *)*p,(void *)p);
      __gen_e_acsl_and_3 = __gen_e_acsl_valid_read_3;
    }
    else __gen_e_acsl_and_3 = 0;
    __e_acsl_assert(__gen_e_acsl_and_3,(char *)"Assertion",(char *)"main",
                    (char *)"\\valid_read(*p)",42);
  }
  char *str[4] =
    {(char *)__gen_e_acsl_literal_string_5,
     (char *)__gen_e_acsl_literal_string_6,
     (char *)__gen_e_acsl_literal_string_7,
     (char *)0};
  __e_acsl_store_block((void *)(str),(size_t)32);
  __e_acsl_full_init((void *)(& str));
  __e_acsl_temporal_store_nblock((void *)(& str[3]),(void *)0);
  __e_acsl_temporal_store_nblock((void *)(& str[2]),
                                 (void *)__gen_e_acsl_literal_string_7);
  __e_acsl_temporal_store_nblock((void *)(& str[1]),
                                 (void *)__gen_e_acsl_literal_string_6);
  __e_acsl_temporal_store_nblock((void *)(str),
                                 (void *)__gen_e_acsl_literal_string_5);
  __e_acsl_temporal_store_nblock((void *)(& p),(void *)(& str));
  __e_acsl_full_init((void *)(& p));
  p = (char **)(& str);
  /*@ assert \valid_read(p); */
  {
    int __gen_e_acsl_initialized_4;
    int __gen_e_acsl_and_4;
    __gen_e_acsl_initialized_4 = __e_acsl_initialized((void *)(& p),
                                                      sizeof(char **));
    if (__gen_e_acsl_initialized_4) {
      int __gen_e_acsl_valid_read_4;
      __gen_e_acsl_valid_read_4 = __e_acsl_valid_read((void *)p,
                                                      sizeof(char *),
                                                      (void *)p,
                                                      (void *)(& p));
      __gen_e_acsl_and_4 = __gen_e_acsl_valid_read_4;
    }
    else __gen_e_acsl_and_4 = 0;
    __e_acsl_assert(__gen_e_acsl_and_4,(char *)"Assertion",(char *)"main",
                    (char *)"\\valid_read(p)",48);
  }
  /*@ assert \valid_read(*p); */
  {
    int __gen_e_acsl_initialized_5;
    int __gen_e_acsl_and_6;
    __gen_e_acsl_initialized_5 = __e_acsl_initialized((void *)p,
                                                      sizeof(char *));
    if (__gen_e_acsl_initialized_5) {
      int __gen_e_acsl_initialized_6;
      int __gen_e_acsl_and_5;
      int __gen_e_acsl_valid_read_6;
      __gen_e_acsl_initialized_6 = __e_acsl_initialized((void *)(& p),
                                                        sizeof(char **));
      if (__gen_e_acsl_initialized_6) {
        int __gen_e_acsl_valid_read_5;
        __gen_e_acsl_valid_read_5 = __e_acsl_valid_read((void *)p,
                                                        sizeof(char *),
                                                        (void *)p,
                                                        (void *)(& p));
        __gen_e_acsl_and_5 = __gen_e_acsl_valid_read_5;
      }
      else __gen_e_acsl_and_5 = 0;
      __e_acsl_assert(__gen_e_acsl_and_5,(char *)"RTE",(char *)"main",
                      (char *)"mem_access: \\valid_read(p)",49);
      __gen_e_acsl_valid_read_6 = __e_acsl_valid_read((void *)*p,
                                                      sizeof(char),
                                                      (void *)*p,(void *)p);
      __gen_e_acsl_and_6 = __gen_e_acsl_valid_read_6;
    }
    else __gen_e_acsl_and_6 = 0;
    __e_acsl_assert(__gen_e_acsl_and_6,(char *)"Assertion",(char *)"main",
                    (char *)"\\valid_read(*p)",49);
  }
  char **P = (char **)(Strings);
  __e_acsl_store_block((void *)(& P),(size_t)8);
  __e_acsl_full_init((void *)(& P));
  __e_acsl_temporal_store_nblock((void *)(& P),(void *)(Strings));
  /*@ assert \valid_read(P); */
  {
    int __gen_e_acsl_initialized_7;
    int __gen_e_acsl_and_7;
    __gen_e_acsl_initialized_7 = __e_acsl_initialized((void *)(& P),
                                                      sizeof(char **));
    if (__gen_e_acsl_initialized_7) {
      int __gen_e_acsl_valid_read_7;
      __gen_e_acsl_valid_read_7 = __e_acsl_valid_read((void *)P,
                                                      sizeof(char *),
                                                      (void *)P,
                                                      (void *)(& P));
      __gen_e_acsl_and_7 = __gen_e_acsl_valid_read_7;
    }
    else __gen_e_acsl_and_7 = 0;
    __e_acsl_assert(__gen_e_acsl_and_7,(char *)"Assertion",(char *)"main",
                    (char *)"\\valid_read(P)",53);
  }
  /*@ assert \valid_read(*P); */
  {
    int __gen_e_acsl_initialized_8;
    int __gen_e_acsl_and_9;
    __gen_e_acsl_initialized_8 = __e_acsl_initialized((void *)P,
                                                      sizeof(char *));
    if (__gen_e_acsl_initialized_8) {
      int __gen_e_acsl_initialized_9;
      int __gen_e_acsl_and_8;
      int __gen_e_acsl_valid_read_9;
      __gen_e_acsl_initialized_9 = __e_acsl_initialized((void *)(& P),
                                                        sizeof(char **));
      if (__gen_e_acsl_initialized_9) {
        int __gen_e_acsl_valid_read_8;
        __gen_e_acsl_valid_read_8 = __e_acsl_valid_read((void *)P,
                                                        sizeof(char *),
                                                        (void *)P,
                                                        (void *)(& P));
        __gen_e_acsl_and_8 = __gen_e_acsl_valid_read_8;
      }
      else __gen_e_acsl_and_8 = 0;
      __e_acsl_assert(__gen_e_acsl_and_8,(char *)"RTE",(char *)"main",
                      (char *)"mem_access: \\valid_read(P)",54);
      __gen_e_acsl_valid_read_9 = __e_acsl_valid_read((void *)*P,
                                                      sizeof(char),
                                                      (void *)*P,(void *)P);
      __gen_e_acsl_and_9 = __gen_e_acsl_valid_read_9;
    }
    else __gen_e_acsl_and_9 = 0;
    __e_acsl_assert(__gen_e_acsl_and_9,(char *)"Assertion",(char *)"main",
                    (char *)"\\valid_read(*P)",54);
  }
  __e_acsl_temporal_store_nblock((void *)(& P),(void *)(& Str));
  __e_acsl_full_init((void *)(& P));
  P = (char **)(& Str);
  /*@ assert \valid_read(P); */
  {
    int __gen_e_acsl_initialized_10;
    int __gen_e_acsl_and_10;
    __gen_e_acsl_initialized_10 = __e_acsl_initialized((void *)(& P),
                                                       sizeof(char **));
    if (__gen_e_acsl_initialized_10) {
      int __gen_e_acsl_valid_read_10;
      __gen_e_acsl_valid_read_10 = __e_acsl_valid_read((void *)P,
                                                       sizeof(char *),
                                                       (void *)P,
                                                       (void *)(& P));
      __gen_e_acsl_and_10 = __gen_e_acsl_valid_read_10;
    }
    else __gen_e_acsl_and_10 = 0;
    __e_acsl_assert(__gen_e_acsl_and_10,(char *)"Assertion",(char *)"main",
                    (char *)"\\valid_read(P)",58);
  }
  /*@ assert \valid_read(*P); */
  {
    int __gen_e_acsl_initialized_11;
    int __gen_e_acsl_and_12;
    __gen_e_acsl_initialized_11 = __e_acsl_initialized((void *)P,
                                                       sizeof(char *));
    if (__gen_e_acsl_initialized_11) {
      int __gen_e_acsl_initialized_12;
      int __gen_e_acsl_and_11;
      int __gen_e_acsl_valid_read_12;
      __gen_e_acsl_initialized_12 = __e_acsl_initialized((void *)(& P),
                                                         sizeof(char **));
      if (__gen_e_acsl_initialized_12) {
        int __gen_e_acsl_valid_read_11;
        __gen_e_acsl_valid_read_11 = __e_acsl_valid_read((void *)P,
                                                         sizeof(char *),
                                                         (void *)P,
                                                         (void *)(& P));
        __gen_e_acsl_and_11 = __gen_e_acsl_valid_read_11;
      }
      else __gen_e_acsl_and_11 = 0;
      __e_acsl_assert(__gen_e_acsl_and_11,(char *)"RTE",(char *)"main",
                      (char *)"mem_access: \\valid_read(P)",59);
      __gen_e_acsl_valid_read_12 = __e_acsl_valid_read((void *)*P,
                                                       sizeof(char),
                                                       (void *)*P,(void *)P);
      __gen_e_acsl_and_12 = __gen_e_acsl_valid_read_12;
    }
    else __gen_e_acsl_and_12 = 0;
    __e_acsl_assert(__gen_e_acsl_and_12,(char *)"Assertion",(char *)"main",
                    (char *)"\\valid_read(*P)",59);
  }
  int extra_lbits[1] = {0};
  __e_acsl_store_block((void *)(extra_lbits),(size_t)4);
  __e_acsl_full_init((void *)(& extra_lbits));
  tree_desc l_desc = {.extra_bits = extra_lbits};
  __e_acsl_store_block((void *)(& l_desc),(size_t)8);
  __e_acsl_full_init((void *)(& l_desc));
  __e_acsl_temporal_store_nblock((void *)(& l_desc.extra_bits),
                                 (void *)(extra_lbits));
  tree_desc descs[2] =
    {{.extra_bits = extra_lbits}, {.extra_bits = extra_lbits}};
  __e_acsl_store_block((void *)(descs),(size_t)16);
  __e_acsl_full_init((void *)(& descs));
  __e_acsl_temporal_store_nblock((void *)(& descs[1].extra_bits),
                                 (void *)(extra_lbits));
  __e_acsl_temporal_store_nblock((void *)(& descs[0].extra_bits),
                                 (void *)(extra_lbits));
  tree_desc2 l_desc2 = {.desc = {.extra_bits = extra_lbits}};
  __e_acsl_store_block((void *)(& l_desc2),(size_t)8);
  __e_acsl_full_init((void *)(& l_desc2));
  __e_acsl_temporal_store_nblock((void *)(& l_desc2.desc.extra_bits),
                                 (void *)(extra_lbits));
  tree_desc2 descs2[2] =
    {{.desc = {.extra_bits = extra_lbits}},
     {.desc = {.extra_bits = extra_lbits}}};
  __e_acsl_store_block((void *)(descs2),(size_t)16);
  __e_acsl_full_init((void *)(& descs2));
  __e_acsl_temporal_store_nblock((void *)(& descs2[1].desc.extra_bits),
                                 (void *)(extra_lbits));
  __e_acsl_temporal_store_nblock((void *)(& descs2[0].desc.extra_bits),
                                 (void *)(extra_lbits));
  __e_acsl_temporal_reset_parameters();
  __e_acsl_temporal_reset_return();
  __e_acsl_temporal_save_nblock_parameter((void *)(& l_desc),0U);
  build_tree(& l_desc);
  __e_acsl_temporal_reset_parameters();
  __e_acsl_temporal_reset_return();
  __e_acsl_temporal_save_nblock_parameter((void *)(descs),0U);
  build_tree(descs);
  __e_acsl_temporal_reset_parameters();
  __e_acsl_temporal_reset_return();
  __e_acsl_temporal_save_nblock_parameter((void *)(& descs[1]),0U);
  build_tree(& descs[1]);
  __e_acsl_temporal_reset_parameters();
  __e_acsl_temporal_reset_return();
  __e_acsl_temporal_save_nblock_parameter((void *)(& l_desc2.desc),0U);
  build_tree(& l_desc2.desc);
  __e_acsl_temporal_reset_parameters();
  __e_acsl_temporal_reset_return();
  __e_acsl_temporal_save_nblock_parameter((void *)(& descs2[0].desc),0U);
  build_tree(& descs2[0].desc);
  __e_acsl_temporal_reset_parameters();
  __e_acsl_temporal_reset_return();
  __e_acsl_temporal_save_nblock_parameter((void *)(& descs2[1].desc),0U);
  build_tree(& descs2[1].desc);
  __retres = 0;
  __e_acsl_delete_block((void *)(Str));
  __e_acsl_delete_block((void *)(Strings));
  __e_acsl_delete_block((void *)(descs2));
  __e_acsl_delete_block((void *)(& l_desc2));
  __e_acsl_delete_block((void *)(descs));
  __e_acsl_delete_block((void *)(& l_desc));
  __e_acsl_delete_block((void *)(extra_lbits));
  __e_acsl_delete_block((void *)(& P));
  __e_acsl_delete_block((void *)(str));
  __e_acsl_delete_block((void *)(& p));
  __e_acsl_delete_block((void *)(strings));
  __e_acsl_memory_clean();
  return __retres;
}


