/* Generated by Frama-C */
#include "stdlib.h"
int A = 0;
int B;
void __e_acsl_globals_init(void)
{
  __e_acsl_store_block((void *)(& B),(size_t)4);
  __e_acsl_full_init((void *)(& B));
  __e_acsl_store_block((void *)(& A),(size_t)4);
  __e_acsl_full_init((void *)(& A));
  return;
}

int main(void)
{
  int __retres;
  int b;
  long *r;
  long d[2];
  int dup[2];
  __e_acsl_memory_init((int *)0,(char ***)0,(size_t)8);
  __e_acsl_globals_init();
  __e_acsl_store_block((void *)(d),(size_t)16);
  __e_acsl_store_block((void *)(& r),(size_t)8);
  __e_acsl_store_block((void *)(& b),(size_t)4);
  int *p = & A;
  __e_acsl_store_block((void *)(& p),(size_t)8);
  __e_acsl_full_init((void *)(& p));
  int *q = & B;
  __e_acsl_store_block((void *)(& q),(size_t)8);
  __e_acsl_full_init((void *)(& q));
  /*@ assert \initialized(&A); */
  __e_acsl_assert(1,(char *)"Assertion",(char *)"main",
                  (char *)"\\initialized(&A)",16);
  /*@ assert \initialized(&B); */
  __e_acsl_assert(1,(char *)"Assertion",(char *)"main",
                  (char *)"\\initialized(&B)",17);
  /*@ assert \initialized(p); */
  {
    int __gen_e_acsl_initialized;
    __gen_e_acsl_initialized = __e_acsl_initialized((void *)p,sizeof(int));
    __e_acsl_assert(__gen_e_acsl_initialized,(char *)"Assertion",
                    (char *)"main",(char *)"\\initialized(p)",18);
  }
  /*@ assert \initialized(q); */
  {
    int __gen_e_acsl_initialized_2;
    __gen_e_acsl_initialized_2 = __e_acsl_initialized((void *)q,sizeof(int));
    __e_acsl_assert(__gen_e_acsl_initialized_2,(char *)"Assertion",
                    (char *)"main",(char *)"\\initialized(q)",19);
  }
  int a = 0;
  __e_acsl_store_block((void *)(& a),(size_t)4);
  __e_acsl_full_init((void *)(& a));
  long c[2] = {(long)1, (long)1};
  __e_acsl_store_block((void *)(c),(size_t)16);
  __e_acsl_full_init((void *)(c));
  __e_acsl_full_init((void *)(& p));
  p = & a;
  __e_acsl_full_init((void *)(& q));
  q = & b;
  /*@ assert \initialized(&a); */
  {
    int __gen_e_acsl_initialized_3;
    __gen_e_acsl_initialized_3 = __e_acsl_initialized((void *)(& a),
                                                      sizeof(int));
    __e_acsl_assert(__gen_e_acsl_initialized_3,(char *)"Assertion",
                    (char *)"main",(char *)"\\initialized(&a)",30);
  }
  /*@ assert ¬\initialized(&b); */
  {
    int __gen_e_acsl_initialized_4;
    __gen_e_acsl_initialized_4 = __e_acsl_initialized((void *)(& b),
                                                      sizeof(int));
    __e_acsl_assert(! __gen_e_acsl_initialized_4,(char *)"Assertion",
                    (char *)"main",(char *)"!\\initialized(&b)",31);
  }
  /*@ assert \initialized(p); */
  {
    int __gen_e_acsl_initialized_5;
    __gen_e_acsl_initialized_5 = __e_acsl_initialized((void *)p,sizeof(int));
    __e_acsl_assert(__gen_e_acsl_initialized_5,(char *)"Assertion",
                    (char *)"main",(char *)"\\initialized(p)",32);
  }
  /*@ assert ¬\initialized(q); */
  {
    int __gen_e_acsl_initialized_6;
    __gen_e_acsl_initialized_6 = __e_acsl_initialized((void *)q,sizeof(int));
    __e_acsl_assert(! __gen_e_acsl_initialized_6,(char *)"Assertion",
                    (char *)"main",(char *)"!\\initialized(q)",33);
  }
  /*@ assert \initialized(&c); */
  {
    int __gen_e_acsl_initialized_7;
    __gen_e_acsl_initialized_7 = __e_acsl_initialized((void *)(& c),
                                                      sizeof(long [2]));
    __e_acsl_assert(__gen_e_acsl_initialized_7,(char *)"Assertion",
                    (char *)"main",(char *)"\\initialized(&c)",34);
  }
  /*@ assert ¬\initialized(&d); */
  {
    int __gen_e_acsl_initialized_8;
    __gen_e_acsl_initialized_8 = __e_acsl_initialized((void *)(& d),
                                                      sizeof(long [2]));
    __e_acsl_assert(! __gen_e_acsl_initialized_8,(char *)"Assertion",
                    (char *)"main",(char *)"!\\initialized(&d)",35);
  }
  __e_acsl_full_init((void *)(& b));
  b = 0;
  /*@ assert \initialized(q); */
  {
    int __gen_e_acsl_initialized_9;
    __gen_e_acsl_initialized_9 = __e_acsl_initialized((void *)q,sizeof(int));
    __e_acsl_assert(__gen_e_acsl_initialized_9,(char *)"Assertion",
                    (char *)"main",(char *)"\\initialized(q)",39);
  }
  /*@ assert \initialized(&b); */
  {
    int __gen_e_acsl_initialized_10;
    __gen_e_acsl_initialized_10 = __e_acsl_initialized((void *)(& b),
                                                       sizeof(int));
    __e_acsl_assert(__gen_e_acsl_initialized_10,(char *)"Assertion",
                    (char *)"main",(char *)"\\initialized(&b)",40);
  }
  __e_acsl_full_init((void *)(& r));
  r = d;
  /*@ assert ¬\initialized((long *)d); */
  {
    int __gen_e_acsl_initialized_11;
    __gen_e_acsl_initialized_11 = __e_acsl_initialized((void *)(d),
                                                       sizeof(long));
    __e_acsl_assert(! __gen_e_acsl_initialized_11,(char *)"Assertion",
                    (char *)"main",(char *)"!\\initialized((long *)d)",43);
  }
  /*@ assert ¬\initialized(&d[1]); */
  {
    int __gen_e_acsl_initialized_12;
    __gen_e_acsl_initialized_12 = __e_acsl_initialized((void *)(& d[1]),
                                                       sizeof(long));
    __e_acsl_assert(! __gen_e_acsl_initialized_12,(char *)"Assertion",
                    (char *)"main",(char *)"!\\initialized(&d[1])",44);
  }
  /*@ assert ¬\initialized(&d); */
  {
    int __gen_e_acsl_initialized_13;
    __gen_e_acsl_initialized_13 = __e_acsl_initialized((void *)(& d),
                                                       sizeof(long [2]));
    __e_acsl_assert(! __gen_e_acsl_initialized_13,(char *)"Assertion",
                    (char *)"main",(char *)"!\\initialized(&d)",45);
  }
  /*@ assert ¬\initialized(r); */
  {
    int __gen_e_acsl_initialized_14;
    __gen_e_acsl_initialized_14 = __e_acsl_initialized((void *)r,
                                                       sizeof(long));
    __e_acsl_assert(! __gen_e_acsl_initialized_14,(char *)"Assertion",
                    (char *)"main",(char *)"!\\initialized(r)",46);
  }
  /*@ assert ¬\initialized(r + 1); */
  {
    int __gen_e_acsl_initialized_15;
    __gen_e_acsl_initialized_15 = __e_acsl_initialized((void *)(r + 1),
                                                       sizeof(long));
    __e_acsl_assert(! __gen_e_acsl_initialized_15,(char *)"Assertion",
                    (char *)"main",(char *)"!\\initialized(r + 1)",47);
  }
  __e_acsl_initialize((void *)(d),sizeof(long));
  d[0] = (long)1;
  /*@ assert \initialized((long *)d); */
  {
    int __gen_e_acsl_initialized_16;
    __gen_e_acsl_initialized_16 = __e_acsl_initialized((void *)(d),
                                                       sizeof(long));
    __e_acsl_assert(__gen_e_acsl_initialized_16,(char *)"Assertion",
                    (char *)"main",(char *)"\\initialized((long *)d)",50);
  }
  /*@ assert ¬\initialized(&d[1]); */
  {
    int __gen_e_acsl_initialized_17;
    __gen_e_acsl_initialized_17 = __e_acsl_initialized((void *)(& d[1]),
                                                       sizeof(long));
    __e_acsl_assert(! __gen_e_acsl_initialized_17,(char *)"Assertion",
                    (char *)"main",(char *)"!\\initialized(&d[1])",51);
  }
  /*@ assert ¬\initialized(&d); */
  {
    int __gen_e_acsl_initialized_18;
    __gen_e_acsl_initialized_18 = __e_acsl_initialized((void *)(& d),
                                                       sizeof(long [2]));
    __e_acsl_assert(! __gen_e_acsl_initialized_18,(char *)"Assertion",
                    (char *)"main",(char *)"!\\initialized(&d)",52);
  }
  /*@ assert \initialized(r); */
  {
    int __gen_e_acsl_initialized_19;
    __gen_e_acsl_initialized_19 = __e_acsl_initialized((void *)r,
                                                       sizeof(long));
    __e_acsl_assert(__gen_e_acsl_initialized_19,(char *)"Assertion",
                    (char *)"main",(char *)"\\initialized(r)",53);
  }
  /*@ assert ¬\initialized(r + 1); */
  {
    int __gen_e_acsl_initialized_20;
    __gen_e_acsl_initialized_20 = __e_acsl_initialized((void *)(r + 1),
                                                       sizeof(long));
    __e_acsl_assert(! __gen_e_acsl_initialized_20,(char *)"Assertion",
                    (char *)"main",(char *)"!\\initialized(r + 1)",54);
  }
  __e_acsl_initialize((void *)(& d[1]),sizeof(long));
  d[1] = (long)1;
  /*@ assert \initialized((long *)d); */
  {
    int __gen_e_acsl_initialized_21;
    __gen_e_acsl_initialized_21 = __e_acsl_initialized((void *)(d),
                                                       sizeof(long));
    __e_acsl_assert(__gen_e_acsl_initialized_21,(char *)"Assertion",
                    (char *)"main",(char *)"\\initialized((long *)d)",57);
  }
  /*@ assert \initialized(&d[1]); */
  {
    int __gen_e_acsl_initialized_22;
    __gen_e_acsl_initialized_22 = __e_acsl_initialized((void *)(& d[1]),
                                                       sizeof(long));
    __e_acsl_assert(__gen_e_acsl_initialized_22,(char *)"Assertion",
                    (char *)"main",(char *)"\\initialized(&d[1])",58);
  }
  /*@ assert \initialized(&d); */
  {
    int __gen_e_acsl_initialized_23;
    __gen_e_acsl_initialized_23 = __e_acsl_initialized((void *)(& d),
                                                       sizeof(long [2]));
    __e_acsl_assert(__gen_e_acsl_initialized_23,(char *)"Assertion",
                    (char *)"main",(char *)"\\initialized(&d)",59);
  }
  /*@ assert \initialized(r); */
  {
    int __gen_e_acsl_initialized_24;
    __gen_e_acsl_initialized_24 = __e_acsl_initialized((void *)r,
                                                       sizeof(long));
    __e_acsl_assert(__gen_e_acsl_initialized_24,(char *)"Assertion",
                    (char *)"main",(char *)"\\initialized(r)",60);
  }
  /*@ assert \initialized(r + 1); */
  {
    int __gen_e_acsl_initialized_25;
    __gen_e_acsl_initialized_25 = __e_acsl_initialized((void *)(r + 1),
                                                       sizeof(long));
    __e_acsl_assert(__gen_e_acsl_initialized_25,(char *)"Assertion",
                    (char *)"main",(char *)"\\initialized(r + 1)",61);
  }
  __e_acsl_full_init((void *)(& p));
  p = (int *)malloc(sizeof(int *));
  /*@ assert ¬\initialized(p); */
  {
    int __gen_e_acsl_initialized_26;
    __gen_e_acsl_initialized_26 = __e_acsl_initialized((void *)p,sizeof(int));
    __e_acsl_assert(! __gen_e_acsl_initialized_26,(char *)"Assertion",
                    (char *)"main",(char *)"!\\initialized(p)",65);
  }
  __e_acsl_full_init((void *)(& q));
  q = (int *)calloc((unsigned long)1,sizeof(int));
  /*@ assert \initialized(q); */
  {
    int __gen_e_acsl_initialized_27;
    __gen_e_acsl_initialized_27 = __e_acsl_initialized((void *)q,sizeof(int));
    __e_acsl_assert(__gen_e_acsl_initialized_27,(char *)"Assertion",
                    (char *)"main",(char *)"\\initialized(q)",69);
  }
  __e_acsl_full_init((void *)(& q));
  q = (int *)realloc((void *)q,(unsigned long)2 * sizeof(int));
  /*@ assert \initialized(q); */
  {
    int __gen_e_acsl_initialized_28;
    __gen_e_acsl_initialized_28 = __e_acsl_initialized((void *)q,sizeof(int));
    __e_acsl_assert(__gen_e_acsl_initialized_28,(char *)"Assertion",
                    (char *)"main",(char *)"\\initialized(q)",74);
  }
  __e_acsl_full_init((void *)(& q));
  q ++;
  /*@ assert ¬\initialized(q); */
  {
    int __gen_e_acsl_initialized_29;
    __gen_e_acsl_initialized_29 = __e_acsl_initialized((void *)q,sizeof(int));
    __e_acsl_assert(! __gen_e_acsl_initialized_29,(char *)"Assertion",
                    (char *)"main",(char *)"!\\initialized(q)",76);
  }
  __e_acsl_full_init((void *)(& q));
  q --;
  free((void *)p);
  free((void *)q);
  /*@ assert ¬\initialized(p); */
  {
    int __gen_e_acsl_initialized_30;
    __gen_e_acsl_initialized_30 = __e_acsl_initialized((void *)p,sizeof(int));
    __e_acsl_assert(! __gen_e_acsl_initialized_30,(char *)"Assertion",
                    (char *)"main",(char *)"!\\initialized(p)",84);
  }
  /*@ assert ¬\initialized(q); */
  {
    int __gen_e_acsl_initialized_31;
    __gen_e_acsl_initialized_31 = __e_acsl_initialized((void *)q,sizeof(int));
    __e_acsl_assert(! __gen_e_acsl_initialized_31,(char *)"Assertion",
                    (char *)"main",(char *)"!\\initialized(q)",85);
  }
  __e_acsl_full_init((void *)(& q));
  q = (int *)(& q - 1024 * 5);
  __e_acsl_full_init((void *)(& q));
  q = (int *)128;
  /*@ assert ¬\initialized(q); */
  {
    int __gen_e_acsl_initialized_32;
    __gen_e_acsl_initialized_32 = __e_acsl_initialized((void *)q,sizeof(int));
    __e_acsl_assert(! __gen_e_acsl_initialized_32,(char *)"Assertion",
                    (char *)"main",(char *)"!\\initialized(q)",93);
  }
  __e_acsl_full_init((void *)(& p));
  p = (int *)0;
  /*@ assert ¬\initialized(p); */
  {
    int __gen_e_acsl_initialized_33;
    __gen_e_acsl_initialized_33 = __e_acsl_initialized((void *)p,sizeof(int));
    __e_acsl_assert(! __gen_e_acsl_initialized_33,(char *)"Assertion",
                    (char *)"main",(char *)"!\\initialized(p)",96);
  }
  int size = 100;
  char *partsc = malloc((unsigned long)size * sizeof(char));
  char *partsi = malloc((unsigned long)size * sizeof(int));
  {
    int i = 0;
    while (i < size) {
      if (i % 2 != 0) 
        /*@ assert Value: mem_access: \valid(partsc + i); */
        *(partsc + i) = (char)'0';
      else 
        /*@ assert Value: mem_access: \valid(partsi + i); */
        *(partsi + i) = (char)0;
      i ++;
    }
  }
  {
    int i_0 = 0;
    while (i_0 < size) {
      if (i_0 % 2 != 0) ;
      i_0 ++;
    }
  }
  dup[0] = 1;
  dup[0] = 1;
  __retres = 0;
  __e_acsl_delete_block((void *)(& B));
  __e_acsl_delete_block((void *)(& A));
  __e_acsl_delete_block((void *)(d));
  __e_acsl_delete_block((void *)(c));
  __e_acsl_delete_block((void *)(& r));
  __e_acsl_delete_block((void *)(& b));
  __e_acsl_delete_block((void *)(& a));
  __e_acsl_delete_block((void *)(& q));
  __e_acsl_delete_block((void *)(& p));
  __e_acsl_memory_clean();
  return __retres;
}


