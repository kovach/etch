#include "stdbool.h"
#include "string.h"
#include <iostream>
#include <stdio.h>
#include <sqlite3.h>
#include <chrono>
#include <float.h>

#define num double
#define ind int

#define macro_ternary(c, x, y) ((c) ? x : y)

//#define time(x, y) \
//  t1 = std::chrono::high_resolution_clock::now(); \
//  val = x(); \
//  t2 = std::chrono::high_resolution_clock::now(); \
//  std::cout << "val: " << val << std::endl; \
//  std::cout << y << " took: " << std::chrono::duration_cast<std::chrono::microseconds>(t2-t1).count() << "μ" << std::endl; \
//  std::cout << y << " took: " << std::chrono::duration_cast<std::chrono::milliseconds>(t2-t1).count() << "ms" << std::endl;

void time(double (* f)(), char const* tag, int reps) {
  auto t1 = std::chrono::high_resolution_clock::now();
  double val;
  for (int i = 0; i < reps; i++) {
    val = f();
  }
  auto t2 = std::chrono::high_resolution_clock::now();
  std::cout << "val: " << val << std::endl;
  std::cout << tag << " took: " << std::chrono::duration_cast<std::chrono::microseconds>(t2-t1).count() << "μ" << std::endl;
  std::cout << tag << " took: " << std::chrono::duration_cast<std::chrono::milliseconds>(t2-t1).count() << "ms" << std::endl;
}

static inline double    num_add(double a, double b) {  return a + b; }
static inline double    num_mul(double a, double b) { return a * b; }
static inline double    num_one() { return 1; }
static inline double    num_zero() { return 0; }

static inline double    num_ofBool(bool x) { return x ? 1 : 0; }
static inline double    num_toMin(double x) { return x; }
static inline double    num_toMax(double x) { return x; }
static inline double    nat_toNum(int x) { return x; }

static inline double    min_add(double a, double b) { return a < b ? a : b; }
static inline double    min_mul(double a, double b) { return a + b; }
static inline double    min_one() { return 0; }
static inline double    min_zero() { return DBL_MAX; }

static inline double    max_add(double a, double b) {  return a < b ? b : a; }
static inline double    max_mul(double a, double b) { return a + b; }
static inline double    max_one() { return 0; }
static inline double    max_zero() { return -DBL_MAX; }

static inline int    nat_add(int a, int b) { return a + b; }
static inline int    nat_mul(int a, int b) { return a * b; }
static inline int    nat_sub(int a, int b) { return a - b; }
static inline bool   nat_lt(int a, int b) { return a < b; }
static inline bool   nat_le(int a, int b) { return a <= b; }
static inline bool   nat_eq(int a, int b) { return a == b; }
static inline int    nat_max(int a, int b) { return a < b ? b : a; }
static inline int    nat_min(int a, int b) { return a < b ? a : b; }
static inline int    TACO_MIN(int a, int b) { return a < b ? a : b; }
static inline int    nat_succ(int a) { return a + 1; }
static inline bool   nat_neg(int a) { return !a; }
static inline int    nat_mid(int a, int b) { return (a + b) / 2; }
static inline int    nat_one() { return 1; }
static inline int    nat_zero() { return 0; }

static inline bool    bool_add(bool a, bool b) { return a || b; }
static inline bool    bool_mul(bool a, bool b) { return a && b; }
static inline bool    bool_one() { return 1; }
static inline bool    bool_zero() { return 0; }
static inline bool    bool_neg(bool x) { return !x; }

static inline bool   str_lt(const char* a, const char* b) { return strcmp(a, b) < 0; }
static inline bool   str_le(const char* a, const char* b) { return strcmp(a, b) <= 0; }
static inline bool   str_eq(const char* a, const char* b) { return strcmp(a, b) == 0; }
static inline int    str_atoi(char* a) { return atoi(a); }
static inline double str_atof(char* a) { return atof(a); }

int dim        = 100000;
int array_size = 100000;

int i1;
int i2;
int i3;
int j1;
int j2;
int j3;
int k1;
int k2;
int k3;

int temp;
bool not_done;
int hi;
int lo;
int m;
int out = 0;
double fout = 0.;

#include "decls.c"

  //printf("reading : %d\n", atoi(argv[0]));
  //printf("reading : %d\n", atoi(argv[1]));
  //printf("reading : %f\n", atof(argv[2]));
static int gen_callback_graph_ssA(void *data, int argc, char **argv, char **azColName){
#include "gen_query_ssA.c"
return 0;
}

static int gen_callback_graph_dsA(void *data, int argc, char **argv, char **azColName){
#include "gen_query_dsA.c"
return 0;
}

static int gen_callback_graph_ssB(void *data, int argc, char **argv, char **azColName){
#include "gen_query_ssB.c"
return 0;
}

static int gen_callback_graph_dsB(void *data, int argc, char **argv, char **azColName){
#include "gen_query_dsB.c"
return 0;
}

static int gen_callback_fires(void *data, int argc, char **argv, char **azColName){
  //printf("reading : %d\n", atoi(argv[0]));
  //printf("reading : %d\n", atoi(argv[1]));
#include "gen_query_fires.c"
return 0;
}

double taco_mul2() {
#include "taco/sum_mul2.c"
}

/* here */
double taco_sum_add2_() {
load_ssA();
load_ssB();
#include "taco/sum_add2.c"
}
double taco_sum_mul2_csr_() {
load_ssA();
load_dsB();
#include "taco/sum_mul2_csr.c"
}
double taco_inner2ss_() {
load_ssA();
load_ssB();
#include "taco/inner2ss.c"
}
/* here end */

static int callback(void *data, int argc, char **argv, char **azColName){
   for(int i = 0; i<argc; i++){
      printf("%s = %s\n", azColName[i], argv[i] ? argv[i] : "NULL");
   }

   printf("\n");
   return 0;
}

// breakpoints
void start() { }
void done() { }

#include "gen_funs.c"


int main() {
  sqlite3* db;
  char* zErrMsg = 0;
  int rc;
  char* data;

  rc = sqlite3_open("/home/scott/Dropbox/2022/pldi.db", &db);

  if(rc) { fprintf(stderr, "Can't open database: %s\n", sqlite3_errmsg(db)); return(0);
  } else { fprintf(stderr, "Opened database successfully\n");
  }

  char const* sql;
  sql = "SELECT * from graph1 ORDER BY src, tgt";
  rc = sqlite3_exec(db, sql, gen_callback_graph_ssA, (void*)data, &zErrMsg);
  rc = sqlite3_exec(db, sql, gen_callback_graph_dsA, (void*)data, &zErrMsg);
  sql = "SELECT * from graph2 ORDER BY src, tgt";
  rc = sqlite3_exec(db, sql, gen_callback_graph_ssB, (void*)data, &zErrMsg);
  rc = sqlite3_exec(db, sql, gen_callback_graph_dsB, (void*)data, &zErrMsg);

  sqlite3_open("/home/scott/Dropbox/2022/etch/etch4/data/FPA_FOD_20170508.sqlite", &db);
  if(rc) { fprintf(stderr, "Can't open database: %s\n", sqlite3_errmsg(db)); return(1);
  } else { fprintf(stderr, "Opened database successfully\n"); }
  sql = "SELECT stat_cause_code, fire_year from fires ORDER BY stat_cause_code, fire_year LIMIT 100";
  rc = sqlite3_exec(db, sql, gen_callback_fires, (void*)data, &zErrMsg);


  if( rc != SQLITE_OK ) {
     fprintf(stderr, "SQL error: %s\n", zErrMsg);
     sqlite3_free(zErrMsg);
     return 1;
  } else {
     fprintf(stdout, "Operation done successfully\n");
  }
  sqlite3_close(db);
  start();

// warmup?
//  fout = 0;
//#include "gen_main.c"
//  taco_mul2();
// warmup

  // decl
  //auto t1 = std::chrono::high_resolution_clock::now();
  //auto t2 = std::chrono::high_resolution_clock::now();
  //int reps = 100;
  //double tout;
  //double val;

#include "gen_out.c"

  return 0;
}
