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
	int n = __VERIFIER_nondet_int();
	__VERIFIER_assume(1<=n && n<=1000);
	int s = 0;
	int j = 0;
	int i = 1;

 while(i <= n) {
    s = s + i;
    j = i;
    i = i + 1;
 }
 static_assert(2*s == n*(n+1));
}

