#include <stdio.h>

#include <iostream>

#include "common.h"
#include "operators.h"
#include "sqlite3.h"

int dim = 100000;
static sqlite3* db;
int res;
double threshold = 0.1;

#define num double
#define ind int

int size[] = {0,0};

int array_size = 4000000;

int dV_i1_;
int dsA_i1_;
int dsB_i1_;
int i1_;
int i2_;
int i3_;
int j1_;
int j2_;
int j3_;
int k1_;
int k2_;
int k3_;

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

ind* ssC1_crd = (ind*)calloc(array_size, sizeof(ind));
ind* ssC1_pos = (ind*)calloc(array_size, sizeof(ind));
ind* ssC2_crd = (ind*)calloc(array_size, sizeof(ind));
ind* ssC2_pos = (ind*)calloc(array_size, sizeof(ind));
ind* ssC3_crd = (ind*)calloc(array_size, sizeof(ind));
ind* ssC3_pos = (ind*)calloc(array_size, sizeof(ind));
num* ssC_vals = (num*)calloc(array_size, sizeof(num));
int  ssC1_i = -1;
int  ssC2_i = -1;
ind ss_C = 0;

ind* ssA1_crd = (ind*)calloc(array_size, sizeof(ind));
ind* ssA1_pos = (ind*)calloc(array_size, sizeof(ind));
ind* ssA2_crd = (ind*)calloc(array_size, sizeof(ind));
ind* ssA2_pos = (ind*)calloc(array_size, sizeof(ind));
num* ssA_vals = (num*)calloc(array_size, sizeof(num));
int  ssA1_i = -1;
int  ssA2_i = -1;
ind  ss_A = 0;

ind* ssF1_crd = (ind*)calloc(array_size, sizeof(ind));
ind* ssF1_pos = (ind*)calloc(array_size, sizeof(ind));
ind* ssF2_crd = (ind*)calloc(array_size, sizeof(ind));
ind* ssF2_pos = (ind*)calloc(array_size, sizeof(ind));
num* ssF_vals = (num*)calloc(array_size, sizeof(num));
int  ssF1_i = -1;
int  ssF2_i = -1;
ind  ss_F = 0;

ind* dsA1_crd = (ind*)calloc(array_size, sizeof(ind));
ind* dsA1_pos = (ind*)calloc(array_size, sizeof(ind));
ind* dsA2_crd = (ind*)calloc(array_size, sizeof(ind));
ind* dsA2_pos = (ind*)calloc(array_size, sizeof(ind));
num* dsA_vals = (num*)calloc(array_size, sizeof(num));
int  dsA1_i = -1;
int  dsA2_i = -1;
ind  ds_A = 0;

ind* ssB1_crd = (ind*)calloc(array_size, sizeof(ind));
ind* ssB1_pos = (ind*)calloc(array_size, sizeof(ind));
ind* ssB2_crd = (ind*)calloc(array_size, sizeof(ind));
ind* ssB2_pos = (ind*)calloc(array_size, sizeof(ind));
num* ssB_vals = (num*)calloc(array_size, sizeof(num));
int  ssB1_i = -1;
int  ssB2_i = -1;
ind  ss_B = 0;

ind* dsB1_crd = (ind*)calloc(array_size, sizeof(ind));
ind* dsB1_pos = (ind*)calloc(array_size, sizeof(ind));
ind* dsB2_crd = (ind*)calloc(array_size, sizeof(ind));
ind* dsB2_pos = (ind*)calloc(array_size, sizeof(ind));
num* dsB_vals = (num*)calloc(array_size, sizeof(num));
int  dsB1_i = -1;
int  dsB2_i = -1;
ind  ds_B = 0;

ind* sV1_pos = (ind*)calloc(array_size, sizeof(ind));
ind* sV1_crd = (ind*)calloc(array_size, sizeof(ind));
num* sV_vals= (num*)calloc(array_size, sizeof(num));;
int  sV1_i = -1;
int  sV2_i = -1;
ind  s_V = 0;

//ind* V1_pos = (ind*)calloc(array_size, sizeof(ind));
//ind* V1_crd = (ind*)calloc(array_size, sizeof(ind));
num* dV_vals= (num*)calloc(array_size, sizeof(num));;
int  dV1_i = -1;
int  dV2_i = -1;
ind  d_V = 0;

ind* V1_pos = (ind*)calloc(array_size, sizeof(ind));
ind* V1_crd = (ind*)calloc(array_size, sizeof(ind));
num* V_vals;
int  V1_i = -1;
int  V2_i = -1;
ind  _V = 0;

int  A1_dimension = dim;
ind* A1_crd;
ind* A1_pos;
ind* A2_crd;
ind* A2_pos;
num* A_vals;
int  A1_i = -1;
int  A2_i = -1;
ind  _A = 0;

int  B1_dimension = dim;
ind* B1_crd;
ind* B1_pos;
ind* B2_crd;
ind* B2_pos;
num* B_vals;
int  B1_i = -1;
int  B2_i = -1;
ind  _B = 0;

ind* dsR1_crd = (ind*)calloc(array_size, sizeof(ind));
ind* dsR1_pos = (ind*)calloc(array_size, sizeof(ind));
ind* dsR2_crd = (ind*)calloc(array_size, sizeof(ind));
ind* dsR2_pos = (ind*)calloc(array_size, sizeof(ind));
num* dsR_vals = (num*)calloc(array_size, sizeof(num));
int  dsR1_i = -1;
int  dsR2_i = -1;
ind  ds_R = 0;

ind* dsS1_crd = (ind*)calloc(array_size, sizeof(ind));
ind* dsS1_pos = (ind*)calloc(array_size, sizeof(ind));
ind* dsS2_crd = (ind*)calloc(array_size, sizeof(ind));
ind* dsS2_pos = (ind*)calloc(array_size, sizeof(ind));
num* dsS_vals = (num*)calloc(array_size, sizeof(num));
int  dsS1_i = -1;
int  dsS2_i = -1;
ind  ds_S = 0;

ind* dsT1_crd = (ind*)calloc(array_size, sizeof(ind));
ind* dsT1_pos = (ind*)calloc(array_size, sizeof(ind));
ind* dsT2_crd = (ind*)calloc(array_size, sizeof(ind));
ind* dsT2_pos = (ind*)calloc(array_size, sizeof(ind));
num* dsT_vals = (num*)calloc(array_size, sizeof(num));
int  dsT1_i = -1;
int  dsT2_i = -1;
ind  ds_T = 0;

void load_ssR() {
A1_crd = dsR1_crd;
A1_pos = dsR1_pos;
A2_crd = dsR2_crd;
A2_pos = dsR2_pos;
A_vals = dsR_vals;
A1_i = -1;
A2_i = -1;
_A = 0;
}

void load_ssT() {
B1_crd = dsT1_crd;
B1_pos = dsT1_pos;
B2_crd = dsT2_crd;
B2_pos = dsT2_pos;
B_vals = dsT_vals;
B1_i = -1;
B2_i = -1;
_B = 0;
}

void load_ssA() {
A1_crd = ssA1_crd;
A1_pos = ssA1_pos;
A2_crd = ssA2_crd;
A2_pos = ssA2_pos;
A_vals = ssA_vals;
A1_i = -1;
A2_i = -1;
_A = 0;
}

void load_dsA() {
A1_crd = dsA1_crd;
A1_pos = dsA1_pos;
A2_crd = dsA2_crd;
A2_pos = dsA2_pos;
A_vals = dsA_vals;
A1_i = -1;
A2_i = -1;
_A = 0;
}

void load_ssB() {
B1_crd = ssB1_crd;
B1_pos = ssB1_pos;
B2_crd = ssB2_crd;
B2_pos = ssB2_pos;
B_vals = ssB_vals;
B1_i = -1;
B2_i = -1;
_B = 0;
}

void load_dsB() {
B1_crd = dsB1_crd;
B1_pos = dsB1_pos;
B2_crd = dsB2_crd;
B2_pos = dsB2_pos;
B_vals = dsB_vals;
B1_i = -1;
B2_i = -1;
_B = 0;
}

void load_dV() {
V_vals = dV_vals;
V1_i = -1;
V2_i = -1;
_V = 0;
}

void load_sV() {
V1_crd = sV1_crd;
V1_pos = sV1_pos;
V_vals = dV_vals;
V1_i = -1;
V2_i = -1;
_V = 0;
}

void load_sssC() {
C1_crd = ssC1_crd;
C1_pos = ssC1_pos;
C2_crd = ssC2_crd;
C2_pos = ssC2_pos;
C3_crd = ssC3_crd;
C3_pos = ssC3_pos;
C_vals = ssC_vals;
C1_i = -1;
C2_i = -1;
_C = 0;
}

/* clang-format off */
#include "taco_kernels.c"

#include "gen_taco.c"
/* clang-format on */

static int populate_taco(sqlite3* db) {
  char* zErrMsg;
  int rc;
  void* data = NULL;

#define GET_TBL2(out_name, tbl_name, col1, col2)                            \
  do {                                                                      \
    rc = sqlite3_exec(                                                      \
        db, "SELECT " #col1 ", " #col2 " FROM " #tbl_name " ORDER BY 1, 2", \
        gen_taco_##out_name##_callback, (void*)data, &zErrMsg);             \
    if (rc != SQLITE_OK) {                                                  \
      printf("%s:%d: %s\n", __FILE__, __LINE__, zErrMsg);                   \
      return rc;                                                            \
    }                                                                       \
  } while (false)

#define GET_TBL3(out_name, tbl_name, col1, col2, col3)                         \
  do {                                                                         \
    rc = sqlite3_exec(db,                                                      \
                      "SELECT " #col1 ", " #col2 ", " #col3 " FROM " #tbl_name \
                      " ORDER BY 1, 2, 3",                                     \
                      gen_taco_##out_name##_callback, (void*)data, &zErrMsg);  \
    if (rc != SQLITE_OK) {                                                     \
      printf("%s:%d: %s\n", __FILE__, __LINE__, zErrMsg);                      \
      return rc;                                                               \
    }                                                                          \
  } while (false)

#define GET_TBL4(out_name, tbl_name, col1, col2, col3, col4)                  \
  do {                                                                        \
    rc = sqlite3_exec(db,                                                     \
                      "SELECT " #col1 ", " #col2 ", " #col3 ", " #col4        \
                      " FROM " #tbl_name " ORDER BY 1, 2, 3, 4",              \
                      gen_taco_##out_name##_callback, (void*)data, &zErrMsg); \
    if (rc != SQLITE_OK) {                                                    \
      printf("%s:%d: %s\n", __FILE__, __LINE__, zErrMsg);                     \
      return rc;                                                              \
    }                                                                         \
  } while (false)

  GET_TBL2(dV, V, i, v);
  GET_TBL2(sV, V, i, v);
  GET_TBL3(dsA, A, i, j, v);
  GET_TBL3(ssA, A, i, j, v);
  GET_TBL3(dsB, B, i, j, v);
  GET_TBL3(ssB, B, i, j, v);
  GET_TBL4(sssC, C, i, j, k, v);

  return rc;
}

void run_all_taco_rep() {
  time(taco_inner2ss, "taco_inner2ss", 50);
  time(etch_inner2ss, "etch_inner2ss", 50);
  printf("\n");
  time(taco_sum_add2, "taco_sum_add2", 50);
  time(etch_sum_add2, "etch_sum_add2", 50);
  printf("\n");
  time(taco_sum_mul2_csr, "taco_sum_mul2_csr", 50);
  time(etch_sum_mul2_csr, "etch_sum_mul2_csr", 50);
  printf("\n");
  time(taco_sum_mul2, "taco_sum_mul2", 50);
  time(etch_sum_mul2, "etch_sum_mul2", 50);
  printf("\n");
  time(taco_mttkrp, "taco_mttkrp", 5);
  time(etch_mttkrp, "etch_mttkrp", 5);
  printf("\n");
  time(taco_spmv, "taco_spmv", 200);
  time(etch_spmv, "etch_spmv", 200);
  printf("\n");
}

int main(int argc, char* argv[]) {
  int rc = SQLITE_OK;

  sqlite3_initialize();
  rc = sqlite3_open(argc > 1 ? argv[1] : "./data/pldi.db", &db);

  if (rc) {
    fprintf(stderr, "Can't open database: %s\n", sqlite3_errmsg(db));
    return 1;
  } else {
    fprintf(stderr, "Opened database successfully\n");
  }

  time([]() { return populate_taco(db); }, "populate_taco", 1);
  printf("Loaded\n");

  run_all_taco_rep();

  sqlite3_close(db);
  return 0;
}
