#if 0
// Not the actual implementations, but substitution rules to make Etch compiler output more readable.
// See Makefile.
#endif

#define num_add(a, b) (a + b)
#define num_mul(a, b) (a * b)
#define num_one() 1
#define num_zero() 0
#define num_lt(a, b) (a < b)
#define num_le(a, b) (a <= b)
#define num_eq(a, b) (a == b)
#define num_max(a, b) max(a, b)
#define num_min(a, b) min(a, b)
#define num_succ(a) (a + 1)
#define num_neg(a) (!a)
#define num_ofBool(x) (x ? 1. : 0.)
#define num_toMin(x) (x)
#define num_toMax(x) (x)
#define num_toNum(x) (x)

#define nat_add(a, b) (a + b)
#define nat_sub(a, b) (a - b)
#define nat_mul(a, b) (a * b)
#define nat_one() 1
#define nat_zero() 0
#define nat_lt(a, b) (a < b)
#define nat_le(a, b) (a <= b)
#define nat_eq(a, b) (a == b)
#define nat_max(a, b) max(a, b)
#define nat_min(a, b) min(a, b)
#define nat_succ(a) (a + 1)
#define nat_neg(a) (!a)

#define bool_add(a, b) (a || b)
#define bool_mul(a, b) (a && b)
#define bool_one() true
#define bool_zero() false
#define bool_neg(a) (!a)
