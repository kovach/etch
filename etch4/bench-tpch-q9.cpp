#include <stdio.h>
#include <time.h>

#include <functional>
#include <iostream>
#include <tuple>
#include <unordered_map>

#include "common.h"
#include "operators.h"
#include "sqlite3.h"

#define TPCH_SF 4

// populated later
int tpch9_lineitem1_pos[2];  // partkey
int tpch9_lineitem1_crd[TPCH_SF * 201000 + 10];
int tpch9_lineitem2_pos[TPCH_SF * 201000 + 10];  // suppkey
int tpch9_lineitem2_crd[TPCH_SF * 801000 + 10];
int tpch9_lineitem3_pos[TPCH_SF * 801000 + 10];  // orderkey
int tpch9_lineitem3_crd[TPCH_SF * 6010000 + 10];
double tpch9_lineitem4_crd[TPCH_SF * 6010000 + 10];  // extendedprice
double tpch9_lineitem5_crd[TPCH_SF * 6010000 + 10];  // discount
double tpch9_lineitem6_crd[TPCH_SF * 6010000 + 10];  // quantity

// tpch9_part1 = partkey (dense)
const char* tpch9_part2_crd[TPCH_SF * 201000 + 10];  // partname

// tpch9_orders1 = orderkey (dense)
int tpch9_orders2_crd[TPCH_SF * 6010000 + 10];  // orderdate

// tpch9_supplier1 = suppkey (dense)
int tpch9_supplier2_crd[TPCH_SF * 11000 + 10];  // nationkey

// tpch9_partsupp1 = partkey (dense)
int tpch9_partsupp2_pos[TPCH_SF * 201000 + 10];  // suppkey
int tpch9_partsupp2_crd[TPCH_SF * 801000 + 10];
double tpch9_partsupp3_crd[TPCH_SF * 801000 + 10];  // supplycost

// tpch9_nation1 = nationkey (dense)
const char* tpch9_nation2_crd[25 + 10];  // nationname

static inline int date_to_year [[gnu::pure]] (std::time_t date) {
  tm result;
  gmtime_r(&date, &result);
  return 1900 + result.tm_year;
}
#include "gen_tpch_q9.c"

#define GEN_D_(tbl_name, crd2copy)                                        \
  static int tbl_name##_i1_ = 0;                                          \
  static int gen_##tbl_name##_callback(void* data, int argc, char** argv, \
                                       char** azColName) {                \
    if (tbl_name##_i1_ <= atoi(argv[0])) {                                \
      tbl_name##_i1_ = atoi(argv[0]) + 1;                                 \
    }                                                                     \
    tbl_name##2_crd [atoi(argv[0])] = crd2copy(argv[1]);                  \
                                                                          \
    return 0;                                                             \
  }

#define PRINT_LENGTH_D_(tbl_name)                       \
  do {                                                  \
    printf("%s2_crd: %d\n", #tbl_name, tbl_name##_i1_); \
  } while (false)

// "is_set" controls whether we assume input keys will be unique
#define GEN_S_(tbl_name, is_set, crd1eq, crd1conv, crd1copy, crd2copy)    \
  static int tbl_name##_out = 0;                                          \
  static int gen_##tbl_name##_callback(void* data, int argc, char** argv, \
                                       char** azColName) {                \
    tbl_name##_out++;                                                     \
    if (!is_set || tbl_name##1_pos [0] == tbl_name##1_pos [1] ||          \
        !crd1eq(crd1conv(argv[0]),                                        \
                tbl_name##1_crd [tbl_name##1_pos [1] - 1])) {             \
      tbl_name##1_pos [1] += 1;                                           \
    }                                                                     \
    tbl_name##1_crd [tbl_name##1_pos [1] - 1] = crd1copy(argv[0]);        \
    tbl_name##2_crd [tbl_name##1_pos [1] - 1] = crd2copy(argv[1]);        \
                                                                          \
    return 0;                                                             \
  }

#define PRINT_LENGTH_S_(tbl_name)                            \
  do {                                                       \
    printf("%s_out: %d\n", #tbl_name, tbl_name##_out);       \
    printf("%s1_pos: %d\n", #tbl_name, 2);                   \
    printf("%s1_crd: %d\n", #tbl_name, tbl_name##1_pos [1]); \
    printf("%s2_crd: %d\n", #tbl_name, tbl_name##1_pos [1]); \
  } while (false)

#define GEN_DS_(tbl_name, is_set, crd2eq, crd2conv, crd2copy, crd3copy)        \
  static int tbl_name##_i1_ = 0;                                               \
  static int gen_##tbl_name##_callback(void* data, int argc, char** argv,      \
                                       char** azColName) {                     \
    while (tbl_name##_i1_ <= atoi(argv[0])) {                                  \
      tbl_name##2_pos [tbl_name##_i1_ + 1] = tbl_name##2_pos [tbl_name##_i1_]; \
      tbl_name##_i1_ += 1;                                                     \
    }                                                                          \
    if (!is_set ||                                                             \
        tbl_name##2_pos [atoi(argv[0])] ==                                     \
            tbl_name##2_pos [atoi(argv[0]) + 1] ||                             \
        !crd2eq(crd2conv(argv[1]),                                             \
                tbl_name##2_crd [tbl_name##2_pos [atoi(argv[0]) + 1] - 1])) {  \
      tbl_name##2_pos [atoi(argv[0]) + 1] += 1;                                \
    }                                                                          \
    tbl_name##2_crd [tbl_name##2_pos [atoi(argv[0]) + 1] - 1] =                \
        crd2copy(argv[1]);                                                     \
    tbl_name##3_crd [tbl_name##2_pos [atoi(argv[0]) + 1] - 1] =                \
        crd3copy(argv[2]);                                                     \
                                                                               \
    return 0;                                                                  \
  }

#define PRINT_LENGTH_DS_(tbl_name)                                        \
  do {                                                                    \
    printf("%s2_pos: %d\n", #tbl_name, tbl_name##_i1_ + 1);               \
    printf("%s2_crd: %d\n", #tbl_name, tbl_name##2_pos [tbl_name##_i1_]); \
    printf("%s3_crd: %d\n", #tbl_name, tbl_name##2_pos [tbl_name##_i1_]); \
  } while (false)

// "is_set" controls whether we assume input keys will be unique
#define GEN_SSS___(tbl_name, is_set, crd1eq, crd1conv, crd1copy, crd2eq,       \
                   crd2conv, crd2copy, crd3eq, crd3conv, crd3copy, crd4copy,   \
                   crd5copy, crd6copy)                                         \
  static int tbl_name##_out = 0;                                               \
  static int gen_##tbl_name##_callback(void* data, int argc, char** argv,      \
                                       char** azColName) {                     \
    tbl_name##_out++;                                                          \
    if (tbl_name##1_pos [0] == tbl_name##1_pos [1] ||                          \
        !crd1eq(crd1conv(argv[0]),                                             \
                tbl_name##1_crd [tbl_name##1_pos [1] - 1])) {                  \
      tbl_name##1_pos [1] += 1;                                                \
      tbl_name##2_pos [tbl_name##1_pos [1]] =                                  \
          tbl_name##2_pos [tbl_name##1_pos [1] - 1];                           \
    }                                                                          \
    tbl_name##1_crd [tbl_name##1_pos [1] - 1] = crd1copy(argv[0]);             \
                                                                               \
    if (tbl_name##2_pos [tbl_name##1_pos [1] - 1] ==                           \
            tbl_name##2_pos [tbl_name##1_pos [1]] ||                           \
        !crd2eq(                                                               \
            crd2conv(argv[1]),                                                 \
            tbl_name##2_crd [tbl_name##2_pos [tbl_name##1_pos [1]] - 1])) {    \
      tbl_name##2_pos [tbl_name##1_pos [1]] += 1;                              \
      tbl_name##3_pos [tbl_name##2_pos [tbl_name##1_pos [1]]] =                \
          tbl_name##3_pos [tbl_name##2_pos [tbl_name##1_pos [1]] - 1];         \
    }                                                                          \
    tbl_name##2_crd [tbl_name##2_pos [tbl_name##1_pos [1]] - 1] =              \
        crd2copy(argv[1]);                                                     \
                                                                               \
    if (!is_set ||                                                             \
        tbl_name##3_pos [tbl_name##2_pos [tbl_name##1_pos [1]] - 1] ==         \
            tbl_name##3_pos [tbl_name##2_pos [tbl_name##1_pos [1]]] ||         \
        !crd3eq(crd3conv(argv[2]),                                             \
                tbl_name##3_crd                                                \
                    [tbl_name##3_pos [tbl_name##2_pos [tbl_name##1_pos [1]]] - \
                     1])) {                                                    \
      tbl_name##3_pos [tbl_name##2_pos [tbl_name##1_pos [1]]] += 1;            \
    }                                                                          \
    tbl_name##3_crd [tbl_name##3_pos [tbl_name##2_pos [tbl_name##1_pos [1]]] - \
                     1] = crd3copy(argv[2]);                                   \
    tbl_name##4_crd [tbl_name##3_pos [tbl_name##2_pos [tbl_name##1_pos [1]]] - \
                     1] = crd4copy(argv[3]);                                   \
    tbl_name##5_crd [tbl_name##3_pos [tbl_name##2_pos [tbl_name##1_pos [1]]] - \
                     1] = crd5copy(argv[4]);                                   \
    tbl_name##6_crd [tbl_name##3_pos [tbl_name##2_pos [tbl_name##1_pos [1]]] - \
                     1] = crd6copy(argv[5]);                                   \
                                                                               \
    return 0;                                                                  \
  }

#define PRINT_LENGTH_SSS___(tbl_name)                                          \
  do {                                                                         \
    printf("%s_out: %d\n", #tbl_name, tbl_name##_out);                         \
    printf("%s1_crd: %d\n", #tbl_name, tbl_name##1_pos [1]);                   \
    printf("%s2_pos: %d\n", #tbl_name, tbl_name##1_pos [1] + 1);               \
    printf("%s2_crd: %d\n", #tbl_name, tbl_name##2_pos [tbl_name##1_pos [1]]); \
    printf("%s2_crd: %d\n", #tbl_name,                                         \
           tbl_name##2_pos [tbl_name##1_pos [1]] + 1);                         \
    printf("%s3_crd: %d\n", #tbl_name,                                         \
           tbl_name##3_pos [tbl_name##2_pos [tbl_name##1_pos [1]]]);           \
    printf("%s4_crd: %d\n", #tbl_name,                                         \
           tbl_name##3_pos [tbl_name##2_pos [tbl_name##1_pos [1]]]);           \
    printf("%s5_crd: %d\n", #tbl_name,                                         \
           tbl_name##3_pos [tbl_name##2_pos [tbl_name##1_pos [1]]]);           \
    printf("%s6_crd: %d\n", #tbl_name,                                         \
           tbl_name##3_pos [tbl_name##2_pos [tbl_name##1_pos [1]]]);           \
  } while (false)

#define EQ(a, b) (a == b)
#define STR_EQ(a, b) (strcmp(a, b) == 0)
#define ID(a) (a)

GEN_SSS___(tpch9_lineitem, false, EQ, atoi, atoi, EQ, atoi, atoi, EQ, atoi,
           atoi, atof, atof, atof)
GEN_D_(tpch9_part, strdup)
GEN_D_(tpch9_orders, atoi)
GEN_D_(tpch9_supplier, atoi)
GEN_DS_(tpch9_partsupp, false, EQ, atoi, atoi, atof)
GEN_D_(tpch9_nation, strdup)

static int populate_tpch_q9(sqlite3* db) {
  char* zErrMsg;
  int rc;
  void* data = NULL;

#define GET_TBL2(tbl_name, col1, col2)                                      \
  do {                                                                      \
    rc = sqlite3_exec(                                                      \
        db, "SELECT " #col1 ", " #col2 " FROM " #tbl_name " ORDER BY 1, 2", \
        gen_tpch9_##tbl_name##_callback, (void*)data, &zErrMsg);            \
    if (rc != SQLITE_OK) {                                                  \
      printf("%s:%d: %s\n", __FILE__, __LINE__, zErrMsg);                   \
      return rc;                                                            \
    }                                                                       \
  } while (false)

#define GET_TBL3(tbl_name, col1, col2, col3)                                   \
  do {                                                                         \
    rc = sqlite3_exec(db,                                                      \
                      "SELECT " #col1 ", " #col2 ", " #col3 " FROM " #tbl_name \
                      " ORDER BY 1, 2, 3",                                     \
                      gen_tpch9_##tbl_name##_callback, (void*)data, &zErrMsg); \
    if (rc != SQLITE_OK) {                                                     \
      printf("%s:%d: %s\n", __FILE__, __LINE__, zErrMsg);                      \
      return rc;                                                               \
    }                                                                          \
  } while (false)

#define GET_TBL6(tbl_name, ...)                                                \
  do {                                                                         \
    rc = sqlite3_exec(db,                                                      \
                      "SELECT " #__VA_ARGS__ " FROM " #tbl_name                \
                      " ORDER BY 1, 2, 3, 4, 5, 6",                            \
                      gen_tpch9_##tbl_name##_callback, (void*)data, &zErrMsg); \
    if (rc != SQLITE_OK) {                                                     \
      printf("%s:%d: %s\n", __FILE__, __LINE__, zErrMsg);                      \
      return rc;                                                               \
    }                                                                          \
  } while (false)

  GET_TBL6(lineitem, l_partkey, l_suppkey, l_orderkey, l_extendedprice,
           l_discount, l_quantity);
  GET_TBL2(part, p_partkey, p_name);
  GET_TBL2(orders, o_orderkey, unixepoch(o_orderdate, 'utc'));
  GET_TBL2(supplier, s_suppkey, s_nationkey);
  GET_TBL3(partsupp, ps_partkey, ps_suppkey, ps_supplycost);
  GET_TBL2(nation, n_nationkey, n_name);

  PRINT_LENGTH_SSS___(tpch9_lineitem);
  PRINT_LENGTH_D_(tpch9_part);
  PRINT_LENGTH_D_(tpch9_orders);
  PRINT_LENGTH_D_(tpch9_supplier);
  PRINT_LENGTH_DS_(tpch9_partsupp);
  PRINT_LENGTH_D_(tpch9_nation);

  return rc;
}

static sqlite3* db;

int main(int argc, char* argv[]) {
  int rc = SQLITE_OK;

  sqlite3_initialize();
  rc = sqlite3_open(argc >= 1 ? argv[1] : "TPC-H.db", &db);

  if (rc) {
    fprintf(stderr, "Can't open database: %s\n", sqlite3_errmsg(db));
    return (0);
  } else {
    fprintf(stderr, "Opened database successfully\n");
  }

  time([]() { return populate_tpch_q9(db); }, "populate_tpch_q9", 1);
  printf("Loaded\n");
  time(q9, "q9", 5);

  sqlite3_close(db);
  return 0;
}
