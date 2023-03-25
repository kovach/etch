#include <stdio.h>

#include <initializer_list>
#include <iostream>
#include <string>

#include "common.h"
#include "operators.h"
#include "sqlite3.h"

int array_size = 4000000;

int* ssA1_pos = (int*)calloc(2, sizeof(int));
int* ssA1_crd = (int*)calloc(array_size, sizeof(int));
int* ssA2_pos = (int*)calloc(array_size, sizeof(int));
int* ssA2_crd = (int*)calloc(array_size, sizeof(int));
double* ssA_vals = (double*)calloc(array_size, sizeof(double));

int* sV1_pos = (int*)calloc(2, sizeof(int));
int* sV1_crd = (int*)calloc(array_size, sizeof(int));
double* sV_vals = (double*)calloc(array_size, sizeof(double));

#include "gen_filtered_spmv.c"

static sqlite3* db;

static int populate_filtered_spmv(sqlite3* db) {
  char* zErrMsg;
  int rc;
  void* data = NULL;

#define GET_TBL2(out_name, tbl_name, ...)                               \
  do {                                                                  \
    rc = sqlite3_exec(                                                  \
        db, "SELECT " #__VA_ARGS__ " FROM " #tbl_name " ORDER BY 1, 2", \
        gen_##out_name##_callback, (void*)data, &zErrMsg);              \
    if (rc != SQLITE_OK) {                                              \
      printf("%s:%d: %s\n", __FILE__, __LINE__, zErrMsg);               \
      return rc;                                                        \
    }                                                                   \
  } while (false)

#define GET_TBL3(out_name, tbl_name, ...)                                  \
  do {                                                                     \
    rc = sqlite3_exec(                                                     \
        db, "SELECT " #__VA_ARGS__ " FROM " #tbl_name " ORDER BY 1, 2, 3", \
        gen_##out_name##_callback, (void*)data, &zErrMsg);                 \
    if (rc != SQLITE_OK) {                                                 \
      printf("%s:%d: %s\n", __FILE__, __LINE__, zErrMsg);                  \
      return rc;                                                           \
    }                                                                      \
  } while (false)

  GET_TBL3(ssA, A, i, j, v);
  GET_TBL2(sV, V, i, v);

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

  time([&rc]() { return rc = populate_filtered_spmv(db); },
       "populate_filtered_spmv", 1);
  if (rc != SQLITE_OK) {
    return 1;
  }
  printf("Loaded\n");

  for (double threshold :
       std::initializer_list<double>{0.0, 0.2, 0.4, 0.6, 0.8, 1.0}) {
    time([threshold]() { return filter_spmv(threshold); },
         ("filter_spmv_" + std::to_string(threshold)).c_str(), 5);
  }

  sqlite3_close(db);
  return 0;
}
