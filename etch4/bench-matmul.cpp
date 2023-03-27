#include <stdio.h>

#include <iostream>

#include "common.h"
#include "operators.h"
#include "sqlite3.h"

int array_size = 4000000;

int* ssA1_crd = (int*)calloc(array_size, sizeof(int));
int* ssA1_pos = (int*)calloc(array_size, sizeof(int));
int* ssA2_crd = (int*)calloc(array_size, sizeof(int));
int* ssA2_pos = (int*)calloc(array_size, sizeof(int));
double* ssA_vals = (double*)calloc(array_size, sizeof(double));
int* ssB1_crd = (int*)calloc(array_size, sizeof(int));
int* ssB1_pos = (int*)calloc(array_size, sizeof(int));
int* ssB2_crd = (int*)calloc(array_size, sizeof(int));
int* ssB2_pos = (int*)calloc(array_size, sizeof(int));
double* ssB_vals = (double*)calloc(array_size, sizeof(double));

#include "gen_matmul.c"

static sqlite3* db;

static int populate_matmul(sqlite3* db) {
  char* zErrMsg;
  int rc;
  void* data = NULL;

#define GET_TBL3(out_name, tbl_name, col1, col2, col3)                         \
  do {                                                                         \
    rc = sqlite3_exec(db,                                                      \
                      "SELECT " #col1 ", " #col2 ", " #col3 " FROM " #tbl_name \
                      " ORDER BY 1, 2, 3",                                     \
                      gen_##out_name##_callback, (void*)data, &zErrMsg);  \
    if (rc != SQLITE_OK) {                                                     \
      printf("%s:%d: %s\n", __FILE__, __LINE__, zErrMsg);                      \
      return rc;                                                               \
    }                                                                          \
  } while (false)

  GET_TBL3(ssA, A, i, j, v);
  GET_TBL3(ssB, B, i, j, v);

  return rc;
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

  time([]() { return populate_matmul(db); }, "populate_matmul", 1);
  printf("Loaded\n");

  time(mul_inner, "mul_inner", 5);
  time(mul_rowcb, "mul_rowcb", 5);

  sqlite3_close(db);
  return 0;
}
