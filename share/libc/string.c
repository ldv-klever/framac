/**************************************************************************/
/*                                                                        */
/*  This file is part of Frama-C.                                         */
/*                                                                        */
/*  Copyright (C) 2007-2013                                               */
/*    CEA (Commissariat à l'énergie atomique et aux énergies              */
/*         alternatives)                                                  */
/*                                                                        */
/*  All rights reserved.                                                  */
/*  Contact CEA LIST for licensing.                                       */
/*                                                                        */
/**************************************************************************/

#include "string.h"

#ifdef __FC_USE_BUILTIN__
#include "__fc_builtin.h"
void* memcpy(void* region1, const void* region2, size_t n)
{
  if (n > 0)
    Frama_C_memcpy(region1, region2, n);
  return region1;
}
#else
void* memcpy(void* region1, const void* region2, size_t n)
{
  const char* first = (const char*)region2;
  const char* last = ((const char*)region2) + n;
  char* result = (char*)region1;
  char* dest = result;
  while (first != last)
    *dest++ = *first++;
  return result;
}
#endif

void* memset (void* dest, int val, size_t len)
{
  unsigned char *ptr = (unsigned char*)dest;
  while (len-- > 0)
    *ptr++ = val;
  return dest;
}

int strcmp(const char *s1, const char *s2)
{
  while (*s1 == *s2++)
    if (*s1++ == '\0')
      return (0);
  return (*(unsigned char *)s1 - *(unsigned char *)--s2);
}

char* strcat(char *s1, const char *s2)
{
  char *os1 = s1;

  while (*s1++)
    ;
  --s1;
  while (*s1++ = *s2++)
    ;
  return (os1);
}

char* strcpy(char *s1, const char *s2)
{
  char *os1 = s1;

  while (*s1++ = *s2++)
    ;
  return (os1);
}

/*
 * Copy s2 to s1, truncating or null-padding to always copy n bytes
 * return s1
 */
char *
strncpy(char *s1, const char *s2, size_t n)
{
  char *os1 = s1;

  n++;
  while ((--n != 0) && ((*s1++ = *s2++) != '\0'))
    ;
  if (n != 0)
    while (--n != 0)
      *s1++ = '\0';
  return (os1);
}

/*
 * Compare strings (at most n bytes)
 *	returns: s1>s2; >0  s1==s2; 0  s1<s2; <0
 */
int
strncmp(const char *s1, const char *s2, size_t n)
{
  n++;
  if (s1 == s2)
    return (0);
  while (--n != 0 && *s1 == *s2++)
    if (*s1++ == '\0')
      return (0);
  return (n == 0 ? 0 : *(unsigned char *)s1 - *(unsigned char *)--s2);
}

size_t
strlen(const char * str)
{
    const char *s =str;
    for (s = str; *s; ++s);
    return(s - str);
}

int
memcmp(const void *s1, const void *s2, size_t n)
{
  if (s1 != s2 && n != 0) {
    const unsigned char	*ps1 = s1;
    const unsigned char	*ps2 = s2;

    do {
      if (*ps1++ != *ps2++)
	return (ps1[-1] - ps2[-1]);
    } while (--n != 0);
  }
  return 0;
}

char *strchr(const char *s, int c)
{ const char ch = c;
  for ( ; *s != ch; s++)
    if (*s == '\0') return 0;
  return (char *)s;
}

char *strrchr(const char *s, int c)
{
    char* ret=0;
    do {
        if( *s == (char)c )
            ret=s;
    } while(*s++);
    return ret;
}

char *strerror(int errnum)
{
  return "strerror message by Frama-C";
}
