#include "stdbool.h"
#include "string.h"
#include <iostream>
#include <stdio.h>
#include <sqlite3.h>
#include <chrono>

#define num double
#define ind int

static inline double    num_add(double a, double b) { return a + b; }
static inline double    num_mul(double a, double b) { return a * b; }
static inline double    num_one() { return 1; }
static inline double    num_zero() { return 0; }

// todo, naming wrong
static inline double    bool_ofBool(bool x) { return x ? 1 : 0; }

static inline int    nat_add(int a, int b) { return a + b; }
static inline int    nat_sub(int a, int b) { return a - b; }
static inline int    nat_mul(int a, int b) { return a * b; }
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

int* base = 0;
int is1_[] = {1,  3,5};
int* is1 = is1_;
int is2_[] = {1,2,3,6};
int* is2 = is2_;
int vs1_[] = {1,  7,3};
int* vs1 = vs1_;
int vs2_[] = {2,2,3,4};
int* vs2 = vs2_;
int p1 = 0;
int p2 = 0;
int s1 = 3;
int s2 = 4;
int temp;
bool not_done;
int hi;
int lo;
int m;
int out = 0;
double fout = 0.;
int i;
int j;
int i1;
int i2;
int i3;
int j1;
int j2;
int j3;
int k1;
int k2;
int k3;
int f1_;
int f2_;

int i_last = -1;
int j_last = -1;

int size[] = {0,0};

ind* out1_crd = (ind*)calloc(array_size, sizeof(ind));
ind* out1_pos = (ind*)calloc(array_size, sizeof(ind));
ind* out2_crd = (ind*)calloc(array_size, sizeof(ind));
ind* out2_pos = (ind*)calloc(array_size, sizeof(ind));
num* out_vals = (num*)calloc(array_size, sizeof(num));
int  out1_i = -1;
int  out2_i = -1;
ind  _out = 0;

ind* C1_crd = (ind*)calloc(array_size, sizeof(ind));
ind* C1_pos = (ind*)calloc(array_size, sizeof(ind));
ind* C2_crd = (ind*)calloc(array_size, sizeof(ind));
ind* C2_pos = (ind*)calloc(array_size, sizeof(ind));
ind* C3_crd = (ind*)calloc(array_size, sizeof(ind));
ind* C3_pos = (ind*)calloc(array_size, sizeof(ind));
num*   C_vals = (num*)calloc(array_size, sizeof(num));
int C1_i = -1;
int C2_i = -1;
ind _C = 0;

int B1_dimension = 10000;
ind* B1_crd = (ind*)calloc(array_size, sizeof(ind));
ind* B1_pos = (ind*)calloc(array_size, sizeof(ind));
ind* B2_crd = (ind*)calloc(array_size, sizeof(ind));
ind* B2_pos = (ind*)calloc(array_size, sizeof(ind));
num*   B_vals = (num*)calloc(array_size, sizeof(num));
int B1_i = -1;
int B2_i = -1;
ind _B = 0;

ind* A1_crd = (ind*)calloc(array_size, sizeof(ind));
ind* A1_pos = (ind*)calloc(array_size, sizeof(ind));
ind* A2_crd = (ind*)calloc(array_size, sizeof(ind));
ind* A2_pos = (ind*)calloc(array_size, sizeof(ind));
num*   A_vals = (num*)calloc(array_size, sizeof(num));
int A1_i = -1;
int A2_i = -1;
ind _A = 0;

int n = 0;
ind* is    = (ind*)calloc(array_size, sizeof(ind));
ind* i_pos = (ind*)calloc(array_size, sizeof(ind));
ind* js    = (ind*)calloc(array_size, sizeof(ind));
ind* j_pos = (ind*)calloc(array_size, sizeof(ind));
num* vals  = (num*)calloc(array_size, sizeof(num));

// not used
struct cursor {
  ind* max; // scalar
  ind* is;  // array
  int* pos; // array
            // is.len = pos.len
};

void push_i(ind i) {
  i_last = i;
  ind& max = n;
  is[max] = i;
  i_pos[max+1] = i_pos[max];
  max++;
}

void push_j(ind j) {
  j_last = j;
  ind* max = &i_pos[n];
  js[*max] = j;
  j_pos[*max+1] = j_pos[*max];
  (*max)++;
}

void push_val(num v) {
  vals[i_pos[n] - 1] = v;
}

// graph: src, tgt, val
static int callback1(void *data, int argc, char **argv, char **azColName){
  ind i = atoi(argv[0]);
  ind j = atoi(argv[1]);
  num v = atof(argv[2]);
  if (i == i_last) {
    //printf("same i\n");
    if (j == j_last) {
      //printf("same j\n");
      // error?
    }
    else {
      //printf("greater j\n");
      push_j(j);
      push_val(v);
    }
  }
  else /* (argv[0] > i_last)*/ {
    //printf("greater i\n");
    push_i(i);
    push_j(j);
    push_val(v);
  }

  return 0;
}

static int gen_callback_graph1(void *data, int argc, char **argv, char **azColName){
#include "gen_query_1.c"
  //printf("reading : %d\n", atoi(argv[0]));
  //printf("reading : %d\n", atoi(argv[1]));
  //printf("reading : %f\n", atof(argv[2]));
return 0;
}

static int gen_callback_graph2(void *data, int argc, char **argv, char **azColName){
#include "gen_query_2.c"
  //printf("reading : %d\n", atoi(argv[0]));
  //printf("reading : %d\n", atoi(argv[1]));
  //printf("reading : %f\n", atof(argv[2]));
return 0;
}

double taco_mul2() {
#include "taco/sum_mul2.c"
}

double taco_mul2_csr() {
#include "taco/sum_mul2_csr.c"
}

double taco_sum_B_csr() {
#include "taco/sum_B_csr.c"
}

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

int main() {
  sqlite3* db;
  char* zErrMsg = 0;
  int rc;
  char* data;

  rc = sqlite3_open("/home/scott/Dropbox/2022/pldi.db", &db);

  if(rc) {
     fprintf(stderr, "Can't open database: %s\n", sqlite3_errmsg(db));
     return(0);
  } else {
     fprintf(stderr, "Opened database successfully\n");
  }

  char const* sql;
  sql = "SELECT * from graph1 ORDER BY src, tgt";
  rc = sqlite3_exec(db, sql, gen_callback_graph1, (void*)data, &zErrMsg);
  sql = "SELECT * from graph2 ORDER BY src, tgt";
  rc = sqlite3_exec(db, sql, gen_callback_graph2, (void*)data, &zErrMsg);


  if( rc != SQLITE_OK ) {
     fprintf(stderr, "SQL error: %s\n", zErrMsg);
     sqlite3_free(zErrMsg);
  } else {
     fprintf(stdout, "Operation done successfully\n");
  }
  sqlite3_close(db);
  start();

  // warmup?
  fout = 0;
#include "gen_main.c"
  taco_mul2();
  // warmup

  // decl
  auto t1 = std::chrono::high_resolution_clock::now();
  auto t2 = std::chrono::high_resolution_clock::now();

  int reps = 100;
  double tout;

  // taco
  t1 = std::chrono::high_resolution_clock::now();
  for (int i = 0; i < reps; i++)
    tout = taco_mul2_csr();
  t2 = std::chrono::high_resolution_clock::now();
  std::cout << "taco took: " << std::chrono::duration_cast<std::chrono::microseconds>(t2-t1).count() << "μ" << std::endl;
  std::cout << "taco took: " << std::chrono::duration_cast<std::chrono::milliseconds>(t2-t1).count() << "ms" << std::endl;
  // taco

/* main code */
  t1 = std::chrono::high_resolution_clock::now();
  for (int i = 0; i < reps; i++) {
  fout = 0;
#include "gen_main.c"
  }
  t2 = std::chrono::high_resolution_clock::now();
  std::cout << "etch took: " << std::chrono::duration_cast<std::chrono::microseconds>(t2-t1).count() << "μ" << std::endl;
  std::cout << "etch took: " << std::chrono::duration_cast<std::chrono::milliseconds>(t2-t1).count() << "ms" << std::endl;
/* end main code */

  done();

  //std::cout << out << std::endl;
  std::cout << "etch: " << fout << std::endl;
  std::cout << "taco: " << tout << std::endl;
  return 0;
}
