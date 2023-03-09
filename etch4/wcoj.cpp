#include "stdbool.h"
#include "string.h"
#include <iostream>
#include <stdio.h>
#include <sqlite3.h>
#include <chrono>
#include <float.h>
#include "math.h"

#define macro_ternary(c, x, y) ((c) ? x : y)

int dim = 10000;

#include "decls.c"

double threshold = 0.1;

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
  //printf("%s out: %f\n", tag, val);
  auto t2 = std::chrono::high_resolution_clock::now();
  std::cout << std::chrono::duration_cast<std::chrono::microseconds>(t2-t1).count() << std::endl;
}

static void sqlite_udf(sqlite3_context *context, int argc, sqlite3_value **argv) {
  int a = sqlite3_value_int(argv[0]);
  int b = sqlite3_value_int(argv[1]);
  double result = sqrt(abs(a - b));
  sqlite3_result_double(context, result);
}

//static inline double    nat_udf(int a, int b) {  /*printf("|%d,%d:%f|", a, b, sqrt(abs(a+b)));*/ return sqrt(abs(a + b)); }
static inline double    udf(int a, int b) { return sqrt(abs(a - b)); }

static inline double    num_add(double a, double b) {  return a + b; }
//#define num_add(a, b) (a + b)
static inline double    num_mul(double a, double b) { return a * b; }
//#define num_mul(a, b) (a * b)
static inline double    num_one() { return 1; }
static inline double    num_zero() { return 0; }
static inline double    num_lt(double a, double b) { return a < b; }
//static inline double    num_lt(double a, double b) { printf("%f < %f\n", a, b); return a < b; }

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
static inline double nat_ofBool(bool x) { return x; }

static inline bool    bool_add(bool a, bool b) { return a || b; }
//#define bool_add(a, b) (a || b)
static inline bool    bool_mul(bool a, bool b) { return a && b; }
//#define bool_mul(a, b) (a && b)
static inline bool    bool_one() { return 1; }
static inline bool    bool_zero() { return 0; }
static inline bool    bool_neg(bool x) { return !x; }

static inline bool   str_lt(const char* a, const char* b) { return strcmp(a, b) < 0; }
static inline bool   str_le(const char* a, const char* b) { return strcmp(a, b) <= 0; }
static inline bool   str_eq(const char* a, const char* b) { return strcmp(a, b) == 0; }
static inline int    str_atoi(char* a) { return atoi(a); }
static inline double str_atof(char* a) { return atof(a); }


int i1_;
int i2_;
int i3_;
int j1_;
int j2_;
int j3_;
int k1_;
int k2_;
int k3_;

int temp;
bool not_done;
int hi;
int lo;
int m;
int out = 0;
double fout = 0.;


  //printf("reading : %d\n", atoi(argv[0]));
  //printf("reading : %d\n", atoi(argv[1]));
  //printf("reading : %f\n", atof(argv[2]));
static int noop(void *data, int argc, char **argv, char **azColName){
return 0;
}
static int print0(void *data, int argc, char **argv, char **azColName){
printf("reading : %d\n", atoi(argv[0]));
return 0;
}

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

static int gen_callback_graph_sssC(void *data, int argc, char **argv, char **azColName){
#include "gen_query_sssC.c"
return 0;
}
static int gen_callback_graph_dV(void *data, int argc, char **argv, char **azColName){
#include "gen_query_dV.c"
return 0;
}
static int gen_callback_graph_sV(void *data, int argc, char **argv, char **azColName){
#include "gen_query_sV.c"
return 0;
}
static int count___ = 0;
static int count_callback(void *data, int argc, char **argv, char **azColName){
  //printf("\n!!\n");
  count___ = atoi(argv[0]);
  //printf("count: %d\n", count___);
  return 0;
}
static double max___ = 0.0;
static int udf_callback(void *data, int argc, char **argv, char **azColName){
  //printf("\n!!\n");
  max___ = atof(argv[0]);
  //printf("count: %d\n", count___);
  return 0;
}
static int gen_callback_wcoj_R(void *data, int argc, char **argv, char **azColName){
#include "gen_query_wcoj_R.c"
return 0;
}
static int gen_callback_wcoj_S(void *data, int argc, char **argv, char **azColName){
#include "gen_query_wcoj_S.c"
return 0;
}
static int gen_callback_wcoj_T(void *data, int argc, char **argv, char **azColName){
#include "gen_query_wcoj_T.c"
return 0;
}
static int gen_callback_udf(void *data, int argc, char **argv, char **azColName){
  printf("udf result: %s\n", argv[0]);
return 0;
}

/* here */
double taco_sum_mul2_() {
load_ssA();
load_ssB();
#include "taco/sum_mul2.c"
}
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

double taco_wcoj() {
load_ssR();
load_ssT();
#include "taco/wcoj.c"
}

double taco_mttkrp_() {
load_dsA();
load_dsB();
load_sssC();
  //printf("TODO\n");
#include "taco/mttkrp.c"
  return 0;
}
double taco_sum_mul2_inner_() {
load_ssA();
load_ssB();
load_dsA();
load_dsB();
#include "taco/sum_mul2_inner.c"
}
double taco_sum_mul2_inner_ss_() {
load_ssA();
load_ssB();
#include "taco/sum_mul2_inner_ss.c"
}
double taco_spmv_() {
load_ssA();
load_dV();
#include "taco/spmv.c"
}
double taco_filter_spmv_() {
//load_sV();
//load_dsA();
//#include "taco/spmv.c"
printf("! dummy function; unrelated to paper results !");
return 0.0;
}
/* here end */

static sqlite3* db;

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

void load_data_of_size(sqlite3* db, int limit)
{
  char sql[256];
  //char const*sq;
  char* zErrMsg = 0;
  int rc;
  char* data;

    sprintf(sql, "SELECT * from (select * from graph1 order by val limit %d) ORDER BY src, tgt", limit);
    ssA1_pos[1] = 0;
    ssB1_pos[1] = 0;
    rc = sqlite3_exec(db, sql, gen_callback_graph_ssA, (void*)data, &zErrMsg);
    rc = sqlite3_exec(db, sql, gen_callback_graph_dsA, (void*)data, &zErrMsg);
    //sq = "SELECT * from graph2 ORDER BY src, tgt";
    sprintf(sql, "SELECT * from (select * from graph2 order by val limit %d) ORDER BY src, tgt", limit);
    rc = sqlite3_exec(db, sql, gen_callback_graph_ssB, (void*)data, &zErrMsg);
    rc = sqlite3_exec(db, sql, gen_callback_graph_dsB, (void*)data, &zErrMsg);
    //printf("loading C\n");
    /* load C */
    sprintf(sql, "SELECT * from (select * from c order by val limit %d) ORDER BY i, j, k", limit);
    rc = sqlite3_exec(db, sql, gen_callback_graph_sssC, (void*)data, &zErrMsg);
    /* load V */
    sprintf(sql, "SELECT * from (select * from v order by val limit %d) ORDER BY i", limit);
    rc = sqlite3_exec(db, sql, gen_callback_graph_dV, (void*)data, &zErrMsg);
    rc = sqlite3_exec(db, sql, gen_callback_graph_sV, (void*)data, &zErrMsg);
}

void test_sample_mv(sqlite3* db) {
  printf("\n\n\n/*** START TEST ***/\n");
  printf("   this tests ETCH's scaling for a filtered operation.\n");
  printf("   cf: Figure 15: Filtered SpMV\n");
  load_data_of_size(db, 100000);

  double init = threshold;
  double limits[] = {0, 0.2, 0.4, 0.6, 0.8, 1.0};
  for(int i = 0; i < 6; i++) {
    printf("testing thresh %f\n", limits[i]);
    threshold = limits[i];
    time(&filter_spmv, "etch", 10);
  }
  threshold = init;
}

void test_triangle() {
  time(&triangle, "etch", 10);
}

double sqlite_triangle() {
  char* zErrMsg = 0;
  char* data;
  //char const* sql = "SELECT count(*) from R";
  char const* sql = "SELECT COUNT(*) from t INNER JOIN (SELECT r.a, s.c from r INNER JOIN s on r.b = s.b) as u on u.a = t.a and u.c = t.c";
  int rc = sqlite3_exec(db, sql, udf_callback, (void*)data, &zErrMsg);
  if (rc) { fprintf(stderr, "SQL error: %s\n", zErrMsg); }
  return max___;
}

int main() {
  char* zErrMsg = 0;
  int rc;
  char* data;

  rc = sqlite3_open("./data/pldi.db", &db);

  if(rc) { fprintf(stderr, "Can't open database: %s\n", sqlite3_errmsg(db)); return(0);
  } else {
  }

  char const* sql;

  rc = sqlite3_exec(db, "SELECT * from r order by A, B", gen_callback_wcoj_R, (void*)data, &zErrMsg);
  if (rc) printf("nope");
  rc = sqlite3_exec(db, "SELECT * from s order by B, C", gen_callback_wcoj_S, (void*)data, &zErrMsg);
  if (rc) printf("nope");
  rc = sqlite3_exec(db, "SELECT * from t order by A, C", gen_callback_wcoj_T, (void*)data, &zErrMsg);
  if (rc) printf("nope");

  time(&sqlite_triangle, "sqlite", 2);
  time(&triangle, "etch", 5000);

  sqlite3_close(db);
  return 0;
}
