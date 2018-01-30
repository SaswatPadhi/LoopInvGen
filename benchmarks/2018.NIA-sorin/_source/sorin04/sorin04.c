extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume(int);
extern int __VERIFIER_nondet_int();
#include <assert.h>

/*
 * Motivation: curious to see if other tools can handle this.
 * This is a really simple benchmark, I'm assuming we have something 
 * similar already?
 */ 

void main()
{
  int i = 0;
  int a = 0;
  int c = 0;
 while(i < 10) {
    c = c + (6*a) + 1;
    a = a + i + 1;
    i = i + 1;
 }
 static_assert(c ==  i*i*i);
}

