#include <stdio.h>

#include <iostream>

#include "common.h"
#include "operators.h"
#include "sqlite3.h"

int dim = 10000;
static sqlite3* db;
int res;
double threshold = 0.1;

/* clang-format off */
#include "decls.c"
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

  run_all_taco();

  sqlite3_close(db);
  return 0;
}
