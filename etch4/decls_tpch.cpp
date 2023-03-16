// TPC-H decls
// This is technically a C file, but it works in C++ too.

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "sqlite3.h"

#define TPCH_SF 4

// populated later
int tpch_lineitem1_pos[TPCH_SF * 1500000 + 10];  // orderkey
int tpch_lineitem1_crd[TPCH_SF * 1500000 + 10];
int tpch_lineitem2_pos[TPCH_SF * 1500000 + 10];  // suppkey
int tpch_lineitem2_crd[TPCH_SF * 6010000 + 10];
double tpch_lineitem3_crd[TPCH_SF * 6010000 + 10];  // extendedprice
double tpch_lineitem4_crd[TPCH_SF * 6010000 + 10];  // discount

// tpch_customer1 = custkey (dense)
int tpch_customer2_pos[TPCH_SF * 150000 + 10];  // nationkey
int tpch_customer2_crd[TPCH_SF * 150000 + 10];

// tpch_orders1 = orderkey (dense)
int tpch_orders2_pos[TPCH_SF * 6010000 + 10];  // orderdate
int tpch_orders2_crd[TPCH_SF * 1500000 + 10];
int tpch_orders3_pos[TPCH_SF * 1500000 + 10];  // custkey
int tpch_orders3_crd[TPCH_SF * 1500000 + 10];

// tpch_supplier1 = suppkey (dense)
int tpch_supplier2_pos[TPCH_SF * 10000 + 10];  // nationkey
int tpch_supplier2_crd[TPCH_SF * 10000 + 10];

// tpch_nation1 = nationkey (dense)
int tpch_nation2_pos[25 + 10];  // regionkey
int tpch_nation2_crd[25 + 10];
char* tpch_nation3_crd[25 + 10];  // nationname

// tpch_region1 = regionkey (dense)
int tpch_region2_pos[5 + 10];  // regionname
char* tpch_region2_crd[5 + 10];

// this is dense-sparse, aka "csr"
#define GEN_DS(tbl_name, is_set, crd2eq, crd2conv, crd2copy)                   \
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
                                                                               \
    return 0;                                                                  \
  }

#define PRINT_LENGTH_DS(tbl_name)                                         \
  do {                                                                    \
    printf("%s2_pos: %d\n", #tbl_name, tbl_name##_i1_ + 1);               \
    printf("%s2_crd: %d\n", #tbl_name, tbl_name##2_pos [tbl_name##_i1_]); \
  } while (false)

// this is sparse-sparse, aka "dcsr"
// "is_set" controls whether we assume input keys will be unique
#define GEN_SS(tbl_name, is_set, crd1eq, crd1conv, crd1copy, crd2eq, crd2conv, \
               crd2copy)                                                       \
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
    if (!is_set ||                                                             \
        tbl_name##2_pos [tbl_name##1_pos [1] - 1] ==                           \
            tbl_name##2_pos [tbl_name##1_pos [1]] ||                           \
        !crd2eq(                                                               \
            crd2conv(argv[1]),                                                 \
            tbl_name##2_crd [tbl_name##2_pos [tbl_name##1_pos [1]] - 1])) {    \
      tbl_name##2_pos [tbl_name##1_pos [1]] += 1;                              \
    }                                                                          \
                                                                               \
    tbl_name##2_crd [tbl_name##2_pos [tbl_name##1_pos [1]] - 1] =              \
        crd2copy(argv[1]);                                                     \
                                                                               \
    return 0;                                                                  \
  }

#define PRINT_LENGTH_SS(tbl_name)                                              \
  do {                                                                         \
    printf("%s total: %d\n", #tbl_name, tbl_name##_out);                       \
    printf("%s1_pos: %d\n", #tbl_name, 1 + 1);                                 \
    printf("%s1_crd: %d\n", #tbl_name, tbl_name##1_pos [1]);                   \
    printf("%s2_pos: %d\n", #tbl_name, tbl_name##1_pos [1] + 1);               \
    printf("%s2_crd: %d\n", #tbl_name, tbl_name##2_pos [tbl_name##1_pos [1]]); \
  } while (false)

#define GEN_DSS(tbl_name, is_set, crd2eq, crd2conv, crd2copy)                  \
  static int tbl_name##_i1_ = 0;                                               \
  static int gen_##tbl_name##_callback(void* data, int argc, char** argv,      \
                                       char** azColName) {                     \
    while ((tbl_name##_i1_ <= atoi(argv[0]))) {                                \
      tbl_name##2_pos [tbl_name##_i1_ + 1] = tbl_name##2_pos [tbl_name##_i1_]; \
      tbl_name##_i1_ += 1;                                                     \
    }                                                                          \
    if (tbl_name##2_pos [atoi(argv[0])] ==                                     \
            tbl_name##2_pos [atoi(argv[0]) + 1] ||                             \
        !crd2eq(crd2conv(argv[1]),                                             \
                tbl_name##2_crd [tbl_name##2_pos [atoi(argv[0]) + 1] - 1])) {  \
      tbl_name##2_pos [atoi(argv[0]) + 1] += 1;                                \
      tbl_name##3_pos [tbl_name##2_pos [atoi(argv[0]) + 1]] =                  \
          tbl_name##3_pos [tbl_name##2_pos [atoi(argv[0]) + 1] - 1];           \
    }                                                                          \
    tbl_name##2_crd [tbl_name##2_pos [atoi(argv[0]) + 1] - 1] =                \
        crd2copy(argv[1]);                                                     \
                                                                               \
    if (!is_set ||                                                             \
        tbl_name##3_pos [tbl_name##2_pos [atoi(argv[0]) + 1] - 1] ==           \
            tbl_name##3_pos [tbl_name##2_pos [atoi(argv[0]) + 1]] ||           \
        atoi(argv[2]) !=                                                       \
            tbl_name##3_crd                                                    \
                [tbl_name##3_pos [tbl_name##2_pos [atoi(argv[0]) + 1]] - 1]) { \
      tbl_name##3_pos [tbl_name##2_pos [atoi(argv[0]) + 1]] += 1;              \
    }                                                                          \
    tbl_name##3_crd [tbl_name##3_pos [tbl_name##2_pos [atoi(argv[0]) + 1]] -   \
                     1] = atoi(argv[2]);                                       \
    return 0;                                                                  \
  }

#define PRINT_LENGTH_DSS(tbl_name)                                            \
  do {                                                                        \
    printf("%s2_pos: %d\n", #tbl_name, tbl_name##_i1_ + 1);                   \
    printf("%s2_crd: %d\n", #tbl_name, tbl_name##2_pos [tbl_name##_i1_]);     \
    printf("%s3_pos: %d\n", #tbl_name, tbl_name##2_pos [tbl_name##_i1_] + 1); \
    printf("%s3_crd: %d\n", #tbl_name,                                        \
           tbl_name##3_pos [tbl_name##2_pos [tbl_name##_i1_]]);               \
  } while (false)

#define GEN_DS_(tbl_name, is_set, crd2eq, crd2conv, crd2copy, crd3copy)        \
  static int tbl_name##_i1_ = 0;                                               \
  static int tbl_name##_out = 0;                                               \
  static int gen_##tbl_name##_callback(void* data, int argc, char** argv,      \
                                       char** azColName) {                     \
    tbl_name##_out += 1;                                                       \
    while ((tbl_name##_i1_ <= atoi(argv[0]))) {                                \
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
    return 0;                                                                  \
  }

#define PRINT_LENGTH_DS_(tbl_name)                                        \
  do {                                                                    \
    printf("%s_out: %d\n", #tbl_name, tbl_name##_out);                    \
    printf("%s2_pos: %d\n", #tbl_name, tbl_name##_i1_ + 1);               \
    printf("%s2_crd: %d\n", #tbl_name, tbl_name##2_pos [tbl_name##_i1_]); \
    printf("%s3_crd: %d\n", #tbl_name, tbl_name##2_pos [tbl_name##_i1_]); \
  } while (false)

// "is_set" controls whether we assume input keys will be unique
#define GEN_SS__(tbl_name, is_set, crd1eq, crd1conv, crd1copy, crd2eq,      \
                 crd2conv, crd2copy, crd3copy, crd4copy)                    \
  static int tbl_name##_out = 0;                                            \
  static int gen_##tbl_name##_callback(void* data, int argc, char** argv,   \
                                       char** azColName) {                  \
    tbl_name##_out++;                                                       \
    if (tbl_name##1_pos [0] == tbl_name##1_pos [1] ||                       \
        !crd1eq(crd1conv(argv[0]),                                          \
                tbl_name##1_crd [tbl_name##1_pos [1] - 1])) {               \
      tbl_name##1_pos [1] += 1;                                             \
      tbl_name##2_pos [tbl_name##1_pos [1]] =                               \
          tbl_name##2_pos [tbl_name##1_pos [1] - 1];                        \
    }                                                                       \
    tbl_name##1_crd [tbl_name##1_pos [1] - 1] = crd1copy(argv[0]);          \
                                                                            \
    if (!is_set ||                                                          \
        tbl_name##2_pos [tbl_name##1_pos [1] - 1] ==                        \
            tbl_name##2_pos [tbl_name##1_pos [1]] ||                        \
        !crd2eq(                                                            \
            crd2conv(argv[1]),                                              \
            tbl_name##2_crd [tbl_name##2_pos [tbl_name##1_pos [1]] - 1])) { \
      tbl_name##2_pos [tbl_name##1_pos [1]] += 1;                           \
    }                                                                       \
    tbl_name##2_crd [tbl_name##2_pos [tbl_name##1_pos [1]] - 1] =           \
        crd2copy(argv[1]);                                                  \
    tbl_name##3_crd [tbl_name##2_pos [tbl_name##1_pos [1]] - 1] =           \
        crd3copy(argv[2]);                                                  \
    tbl_name##4_crd [tbl_name##2_pos [tbl_name##1_pos [1]] - 1] =           \
        crd4copy(argv[3]);                                                  \
                                                                            \
    return 0;                                                               \
  }

#define PRINT_LENGTH_SS__(tbl_name)                                            \
  do {                                                                         \
    printf("%s_out: %d\n", #tbl_name, tbl_name##_out);                         \
    printf("%s1_crd: %d\n", #tbl_name, tbl_name##1_pos [1]);                   \
    printf("%s2_pos: %d\n", #tbl_name, tbl_name##1_pos [1] + 1);               \
    printf("%s2_crd: %d\n", #tbl_name, tbl_name##2_pos [tbl_name##1_pos [1]]); \
    printf("%s3_crd: %d\n", #tbl_name, tbl_name##2_pos [tbl_name##1_pos [1]]); \
    printf("%s4_crd: %d\n", #tbl_name, tbl_name##2_pos [tbl_name##1_pos [1]]); \
  } while (false)

#define EQ(a, b) (a == b)
#define STR_EQ(a, b) (strcmp(a, b) == 0)
#define ID(a) (a)

GEN_SS__(tpch_lineitem, false, EQ, atoi, atoi, EQ, atoi, atoi, atof, atof)
GEN_DS(tpch_customer, false, EQ, atoi, atoi)
GEN_DSS(tpch_orders, false, EQ, atoi, atoi)
GEN_DS(tpch_supplier, false, EQ, atoi, atoi)
GEN_DS_(tpch_nation, false, EQ, atoi, atoi, strdup)
GEN_DS(tpch_region, false, STR_EQ, ID, strdup)

static int populate_tpch(sqlite3* db) {
  char* zErrMsg;
  int rc;
  void* data = NULL;

#define GET_TBL2(tbl_name, col1, col2)                                      \
  do {                                                                      \
    rc = sqlite3_exec(                                                      \
        db, "SELECT " #col1 ", " #col2 " FROM " #tbl_name " ORDER BY 1, 2", \
        gen_tpch_##tbl_name##_callback, (void*)data, &zErrMsg);             \
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
                      gen_tpch_##tbl_name##_callback, (void*)data, &zErrMsg);  \
    if (rc != SQLITE_OK) {                                                     \
      printf("%s:%d: %s\n", __FILE__, __LINE__, zErrMsg);                      \
      return rc;                                                               \
    }                                                                          \
  } while (false)

#define GET_TBL4(tbl_name, col1, col2, col3, col4)                            \
  do {                                                                        \
    rc = sqlite3_exec(db,                                                     \
                      "SELECT " #col1 ", " #col2 ", " #col3 ", " #col4        \
                      " FROM " #tbl_name " ORDER BY 1, 2, 3, 4",              \
                      gen_tpch_##tbl_name##_callback, (void*)data, &zErrMsg); \
    if (rc != SQLITE_OK) {                                                    \
      printf("%s:%d: %s\n", __FILE__, __LINE__, zErrMsg);                     \
      return rc;                                                              \
    }                                                                         \
  } while (false)

  GET_TBL4(lineitem, l_orderkey, l_suppkey, l_extendedprice, l_discount);
  GET_TBL2(customer, c_custkey, c_nationkey);
  GET_TBL3(orders, o_orderkey, unixepoch(o_orderdate, 'utc'), o_custkey);
  GET_TBL2(supplier, s_suppkey, s_nationkey);
  GET_TBL3(nation, n_nationkey, n_regionkey, n_name);
  GET_TBL2(region, r_regionkey, r_name);

  PRINT_LENGTH_SS__(tpch_lineitem);
  PRINT_LENGTH_DSS(tpch_orders);
  PRINT_LENGTH_DS(tpch_customer);
  PRINT_LENGTH_DS(tpch_supplier);
  PRINT_LENGTH_DS_(tpch_nation);
  PRINT_LENGTH_DS(tpch_region);

  return rc;
}
