#include <float.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>

static inline double num_add(double a, double b) { return a + b; }
static inline double num_sub(double a, double b) { return a - b; }
static inline double num_mul(double a, double b) { return a * b; }
static inline double num_one() { return 1; }
static inline double num_zero() { return 0; }
static inline double num_lt(double a, double b) { return a < b; }
static inline double num_le(double a, double b) { return a <= b; }
// static inline double num_lt(double a, double b) { printf("%f < %f\n", a,
// b); return a < b; }

static inline double num_ofBool(bool x) { return x ? 1 : 0; }
static inline double num_toMin(double x) { return x; }
static inline double num_toMax(double x) { return x; }
static inline double nat_toNum(int x) { return x; }

static inline double min_add(double a, double b) { return a < b ? a : b; }
static inline double min_mul(double a, double b) { return a + b; }
static inline double min_one() { return 0; }
static inline double min_zero() { return DBL_MAX; }

static inline double max_add(double a, double b) { return a < b ? b : a; }
static inline double max_mul(double a, double b) { return a + b; }
static inline double max_one() { return 0; }
static inline double max_zero() { return -DBL_MAX; }

static inline int nat_add(int a, int b) { return a + b; }
static inline int nat_mul(int a, int b) { return a * b; }
static inline int nat_sub(int a, int b) { return a - b; }
static inline bool nat_lt(int a, int b) { return a < b; }
static inline bool nat_le(int a, int b) { return a <= b; }
static inline bool nat_eq(int a, int b) { return a == b; }
static inline int nat_max(int a, int b) { return a < b ? b : a; }
static inline int nat_min(int a, int b) { return a < b ? a : b; }
static inline int nat_succ(int a) { return a + 1; }
static inline int nat_mid(int a, int b) { return (a + b) / 2; }
static inline int nat_one() { return 1; }
static inline int nat_zero() { return 0; }
static inline int nat_ofBool(bool x) { return x; }

static inline int int_add(int a, int b) { return a + b; }
static inline int int_mul(int a, int b) { return a * b; }
static inline int int_sub(int a, int b) { return a - b; }
static inline bool int_lt(int a, int b) { return a < b; }
static inline bool int_le(int a, int b) { return a <= b; }
static inline bool int_eq(int a, int b) { return a == b; }
static inline int int_max(int a, int b) { return a < b ? b : a; }
static inline int int_min(int a, int b) { return a < b ? a : b; }
static inline int int_succ(int a) { return a + 1; }
static inline bool int_neg(int a) { return !a; }
static inline int int_mid(int a, int b) { return (a + b) / 2; }
static inline int int_one() { return 1; }
static inline int int_zero() { return 0; }
static inline int int_ofBool(bool x) { return x; }

// static inline bool bool_add(bool a, bool b) { return a || b; }
// static inline bool bool_mul(bool a, bool b) { return a && b; }
#define bool_add(a, b) ((a) || (b))
#define bool_mul(a, b) ((a) && (b))
static inline bool bool_one() { return true; }
static inline bool bool_zero() { return false; }
static inline bool bool_neg(bool x) { return !x; }

// Treat NULL as the top value (e.g., empty space at the end of the array).
static inline const char* str_zero() { return ""; }
static inline bool str_lt(const char* a, const char* b) {
  if (!a) return false;
  if (!b) return true;
  return strcmp(a, b) < 0;
}
static inline bool str_le(const char* a, const char* b) {
  if (!a) return !b;
  if (!b) return true;
  return strcmp(a, b) <= 0;
}
static inline int str_find(const char* haystack, const char* needle) {
  if (!haystack) return -1;
  const char* res = strstr(haystack, needle);
  if (!res) return -1;
  return res - haystack;
}
static inline const char* str_max(const char* a, const char* b) {
  return str_lt(a, b) ? b : a;
}
static inline const char* str_min(const char* a, const char* b) {
  return str_lt(a, b) ? a : b;
}
static inline bool str_eq(const char* a, const char* b) {
  if (!a || !b) return a == b;
  return strcmp(a, b) == 0;
}
static inline int str_atoi(const char* a) { return atoi(a); }
static inline double str_atof(const char* a) { return atof(a); }

#define TACO_MIN(a, b) ((a) < (b) ? (a) : (b))

#define macro_ternary(c, x, y) ((c) ? x : y)
#define index_map(a, ...) &a[{__VA_ARGS__}]
