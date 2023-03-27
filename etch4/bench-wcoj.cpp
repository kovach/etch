#include <stdio.h>

#include <iostream>

#include "common.h"
#include "operators.h"
#include "sqlite3.h"

// populated later
#define MAX_SCALE 1000000

int dsR1_pos[2];
int dsR1_crd[MAX_SCALE + 10];
int dsR2_pos[MAX_SCALE + 10];
int dsR2_crd[2 * MAX_SCALE + 10];
int dsS1_pos[2];
int dsS1_crd[MAX_SCALE + 10];
int dsS2_pos[MAX_SCALE + 10];
int dsS2_crd[2 * MAX_SCALE + 10];
int dsT1_pos[2];
int dsT1_crd[MAX_SCALE + 10];
int dsT2_pos[MAX_SCALE + 10];
int dsT2_crd[2 * MAX_SCALE + 10];

#include "gen_wcoj.c"

static int populate_wcoj(sqlite3* db) {
  char* zErrMsg;
  int rc;
  void* data = NULL;

#define GET_TBL2(tbl_name, col1, col2)                                      \
  do {                                                                      \
    rc = sqlite3_exec(                                                      \
        db, "SELECT " #col1 ", " #col2 " FROM " #tbl_name " ORDER BY 1, 2", \
        gen_callback_wcoj_##tbl_name, (void*)data, &zErrMsg);    \
    if (rc != SQLITE_OK) {                                                  \
      printf("%s:%d: %s\n", __FILE__, __LINE__, zErrMsg);                   \
      return rc;                                                            \
    }                                                                       \
  } while (false)

  GET_TBL2(R, a, b);
  GET_TBL2(S, b, c);
  GET_TBL2(T, a, c);

  return rc;
}

static sqlite3* db;
int res;

int main(int argc, char* argv[]) {
  int rc = SQLITE_OK;

  sqlite3_initialize();
  rc = sqlite3_open(argc >= 1 ? argv[1] : "data/pldi.db", &db);

  if (rc) {
    fprintf(stderr, "Can't open database: %s\n", sqlite3_errmsg(db));
    return (0);
  } else {
    fprintf(stderr, "Opened database successfully\n");
  }

  time([]() { return populate_wcoj(db); }, "populate_wcoj", 1);
  printf("Loaded\n");

  time([&]() {
    for (int i = 0; i < 1000; ++i) {
        res = wcoj();
    }
    return res;
  }, "wcojx1000", 5);

  sqlite3_close(db);
  return 0;
}
