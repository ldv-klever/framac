/* Generated by Frama-C */
#include "stdio.h"
#include "stdlib.h"
int main(void)
{
  int __retres;
  __e_acsl_memory_init((int *)0,(char ***)0,(size_t)8);
  int x = 0;
  int y = 1;
  /*@ assert x ≡ 0 ∧ y ≡ 1; */
  {
    int __gen_e_acsl_and;
    if (x == 0) __gen_e_acsl_and = y == 1; else __gen_e_acsl_and = 0;
    __e_acsl_assert(__gen_e_acsl_and,(char *)"Assertion",(char *)"main",
                    (char *)"x == 0 && y == 1",9);
  }
  /*@ assert ¬(x ≢ 0 ∧ y ≡ 1 / 0); */
  {
    int __gen_e_acsl_and_2;
    if (x != 0) {
      __e_acsl_assert(0,(char *)"RTE",(char *)"main",
                      (char *)"division_by_zero: 0 != 0",10);
      __gen_e_acsl_and_2 = y == 1 / 0;
    }
    else __gen_e_acsl_and_2 = 0;
    __e_acsl_assert(! __gen_e_acsl_and_2,(char *)"Assertion",(char *)"main",
                    (char *)"!(x != 0 && y == 1 / 0)",10);
  }
  /*@ assert y ≡ 1 ∨ x ≡ 1; */
  {
    int __gen_e_acsl_or;
    if (y == 1) __gen_e_acsl_or = 1; else __gen_e_acsl_or = x == 1;
    __e_acsl_assert(__gen_e_acsl_or,(char *)"Assertion",(char *)"main",
                    (char *)"y == 1 || x == 1",11);
  }
  /*@ assert x ≡ 0 ∨ y ≡ 1 / 0; */
  {
    int __gen_e_acsl_or_2;
    if (x == 0) __gen_e_acsl_or_2 = 1;
    else {
      __e_acsl_assert(0,(char *)"RTE",(char *)"main",
                      (char *)"division_by_zero: 0 != 0",12);
      __gen_e_acsl_or_2 = y == 1 / 0;
    }
    __e_acsl_assert(__gen_e_acsl_or_2,(char *)"Assertion",(char *)"main",
                    (char *)"x == 0 || y == 1 / 0",12);
  }
  /*@ assert x ≡ 0 ⇒ y ≡ 1; */
  {
    int __gen_e_acsl_implies;
    if (! (x == 0)) __gen_e_acsl_implies = 1;
    else __gen_e_acsl_implies = y == 1;
    __e_acsl_assert(__gen_e_acsl_implies,(char *)"Assertion",(char *)"main",
                    (char *)"x == 0 ==> y == 1",13);
  }
  /*@ assert x ≡ 1 ⇒ y ≡ 1 / 0; */
  {
    int __gen_e_acsl_implies_2;
    if (! (x == 1)) __gen_e_acsl_implies_2 = 1;
    else {
      __e_acsl_assert(0,(char *)"RTE",(char *)"main",
                      (char *)"division_by_zero: 0 != 0",14);
      __gen_e_acsl_implies_2 = y == 1 / 0;
    }
    __e_acsl_assert(__gen_e_acsl_implies_2,(char *)"Assertion",
                    (char *)"main",(char *)"x == 1 ==> y == 1 / 0",14);
  }
  /*@ assert x ≢ 0? x ≢ 0: y ≢ 0; */
  {
    int __gen_e_acsl_if;
    if (x != 0) __gen_e_acsl_if = x != 0; else __gen_e_acsl_if = y != 0;
    __e_acsl_assert(__gen_e_acsl_if,(char *)"Assertion",(char *)"main",
                    (char *)"x != 0? x != 0: y != 0",15);
  }
  /*@ assert y ≢ 0? y ≢ 0: x ≢ 0; */
  {
    int __gen_e_acsl_if_2;
    if (y != 0) __gen_e_acsl_if_2 = y != 0; else __gen_e_acsl_if_2 = x != 0;
    __e_acsl_assert(__gen_e_acsl_if_2,(char *)"Assertion",(char *)"main",
                    (char *)"y != 0? y != 0: x != 0",16);
  }
  /*@ assert x ≡ 1? x ≡ 18: x ≡ 0; */
  {
    int __gen_e_acsl_if_3;
    if (x == 1) __gen_e_acsl_if_3 = x == 18; else __gen_e_acsl_if_3 = x == 0;
    __e_acsl_assert(__gen_e_acsl_if_3,(char *)"Assertion",(char *)"main",
                    (char *)"x == 1? x == 18: x == 0",17);
  }
  /*@ assert x ≡ 2 ⇔ y ≡ 3; */
  {
    int __gen_e_acsl_implies_3;
    int __gen_e_acsl_equiv;
    if (! (x == 2)) __gen_e_acsl_implies_3 = 1;
    else __gen_e_acsl_implies_3 = y == 3;
    if (__gen_e_acsl_implies_3) {
      int __gen_e_acsl_implies_4;
      if (! (y == 3)) __gen_e_acsl_implies_4 = 1;
      else __gen_e_acsl_implies_4 = x == 2;
      __gen_e_acsl_equiv = __gen_e_acsl_implies_4;
    }
    else __gen_e_acsl_equiv = 0;
    __e_acsl_assert(__gen_e_acsl_equiv,(char *)"Assertion",(char *)"main",
                    (char *)"x == 2 <==> y == 3",20);
  }
  /*@ assert x ≡ 0 ⇔ y ≡ 1; */
  {
    int __gen_e_acsl_implies_5;
    int __gen_e_acsl_equiv_2;
    if (! (x == 0)) __gen_e_acsl_implies_5 = 1;
    else __gen_e_acsl_implies_5 = y == 1;
    if (__gen_e_acsl_implies_5) {
      int __gen_e_acsl_implies_6;
      if (! (y == 1)) __gen_e_acsl_implies_6 = 1;
      else __gen_e_acsl_implies_6 = x == 0;
      __gen_e_acsl_equiv_2 = __gen_e_acsl_implies_6;
    }
    else __gen_e_acsl_equiv_2 = 0;
    __e_acsl_assert(__gen_e_acsl_equiv_2,(char *)"Assertion",(char *)"main",
                    (char *)"x == 0 <==> y == 1",21);
  }
  /*@ assert ((x ≢ 0? x: y) ≢ 0) ≡ (x ≡ 0); */
  {
    int __gen_e_acsl_if_4;
    if (x != 0) __gen_e_acsl_if_4 = x; else __gen_e_acsl_if_4 = y;
    __e_acsl_assert((__gen_e_acsl_if_4 != 0) == (x == 0),(char *)"Assertion",
                    (char *)"main",
                    (char *)"((x != 0? x: y) != 0) == (x == 0)",24);
  }
  /*@ assert (x ≢ 0 ∧ y ≢ 0) ∨ y ≢ 0; */
  {
    int __gen_e_acsl_and_3;
    int __gen_e_acsl_or_3;
    if (x != 0) __gen_e_acsl_and_3 = y != 0; else __gen_e_acsl_and_3 = 0;
    if (__gen_e_acsl_and_3) __gen_e_acsl_or_3 = 1;
    else __gen_e_acsl_or_3 = y != 0;
    __e_acsl_assert(__gen_e_acsl_or_3,(char *)"Assertion",(char *)"main",
                    (char *)"(x != 0 && y != 0) || y != 0",25);
  }
  /*@ assert (x ≢ 0 ∨ y ≢ 0) ∧ y ≡ 1; */
  {
    int __gen_e_acsl_or_4;
    int __gen_e_acsl_and_4;
    if (x != 0) __gen_e_acsl_or_4 = 1; else __gen_e_acsl_or_4 = y != 0;
    if (__gen_e_acsl_or_4) __gen_e_acsl_and_4 = y == 1;
    else __gen_e_acsl_and_4 = 0;
    __e_acsl_assert(__gen_e_acsl_and_4,(char *)"Assertion",(char *)"main",
                    (char *)"(x != 0 || y != 0) && y == 1",26);
  }
  /*@ assert (x ≢ 0 ∨ y ≢ 0) ≡ (y ≢ 0); */
  {
    int __gen_e_acsl_or_5;
    if (x != 0) __gen_e_acsl_or_5 = 1; else __gen_e_acsl_or_5 = y != 0;
    __e_acsl_assert(__gen_e_acsl_or_5 == (y != 0),(char *)"Assertion",
                    (char *)"main",(char *)"(x != 0 || y != 0) == (y != 0)",
                    27);
  }
  /*@ assert (x ≢ 0 ∧ y ≢ 0) ≡ (x ≢ 0); */
  {
    int __gen_e_acsl_and_5;
    if (x != 0) __gen_e_acsl_and_5 = y != 0; else __gen_e_acsl_and_5 = 0;
    __e_acsl_assert(__gen_e_acsl_and_5 == (x != 0),(char *)"Assertion",
                    (char *)"main",(char *)"(x != 0 && y != 0) == (x != 0)",
                    28);
  }
  __retres = 0;
  return __retres;
}


