extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
#include <assert.h>

void main()
{
  int j=0; int i=0;
  int k = __VERIFIER_nondet_int();
  __VERIFIER_assume(k > 0);

  while(j < k) { // invariant i == 2*k*j
    i = i + 2*k;
    j = j + 1;
  }
  static_assert(i == 2*k*j);
}

