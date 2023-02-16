// TPC-H decls
// sorry

#include <stdio.h>
#include <stdlib.h>
#include "sqlite3.h"

constexpr int TPCH_ARRAY_SIZE = 10000000;

// populated later
int ASIA;

int tpch_lineitem1_pos[TPCH_ARRAY_SIZE];  // orderkey
int tpch_lineitem1_crd[TPCH_ARRAY_SIZE];
int tpch_lineitem2_pos[TPCH_ARRAY_SIZE];  // suppkey
int tpch_lineitem2_crd[TPCH_ARRAY_SIZE];
double tpch_lineitem_vals[TPCH_ARRAY_SIZE];
  // supposed to be l_extendedprice * (1 - l_discount)

// tpch_customer1 = custkey (dense)
int tpch_customer2_pos[TPCH_ARRAY_SIZE];  // nationkey
int tpch_customer2_crd[TPCH_ARRAY_SIZE];

int tpch_orders1_pos[TPCH_ARRAY_SIZE];  // custkey
int tpch_orders1_crd[TPCH_ARRAY_SIZE];
int tpch_orders2_pos[TPCH_ARRAY_SIZE];  // orderkey
int tpch_orders2_crd[TPCH_ARRAY_SIZE];

int tpch_supplier1_pos[TPCH_ARRAY_SIZE];  // nationkey
int tpch_supplier1_crd[TPCH_ARRAY_SIZE];
int tpch_supplier2_pos[TPCH_ARRAY_SIZE];  // suppkey
int tpch_supplier2_crd[TPCH_ARRAY_SIZE];

// tpch_nation1 = nationkey (dense)
int tpch_nation2_pos[TPCH_ARRAY_SIZE];  // regionkey
int tpch_nation2_crd[TPCH_ARRAY_SIZE];

// this is the "mat" type, aka "dcsr"
#define GEN_MAT(tbl_name)                                                  \
  static int gen_##tbl_name##_callback(void* data, int argc, char** argv,  \
                                       char** azColName) {                 \
    if (tbl_name##1_pos [0] == tbl_name##1_pos [1] ||                      \
        atoi(argv[0]) != tbl_name##1_crd [tbl_name##1_pos [1] - 1]) {      \
      tbl_name##1_pos [1] = (tbl_name##1_pos [1] + 1);                     \
      tbl_name##2_pos [((tbl_name##1_pos [1] - 1) + 1)] =                  \
          tbl_name##2_pos [(tbl_name##1_pos [1] - 1)];                     \
    }                                                                      \
    tbl_name##1_crd [tbl_name##1_pos [1] - 1] = atoi(argv[0]);             \
                                                                           \
    if (tbl_name##2_pos [tbl_name##1_pos [1] - 1] ==                       \
            tbl_name##2_pos [tbl_name##1_pos [1]] ||                       \
        atoi(argv[1]) !=                                                   \
            tbl_name##2_crd [tbl_name##2_pos [tbl_name##1_pos [1]] - 1]) { \
      tbl_name##2_pos [tbl_name##1_pos [1]] += 1;                          \
      tbl_name##_vals[tbl_name##2_pos [tbl_name##1_pos [1]] - 1] = 0;      \
    }                                                                      \
                                                                           \
    tbl_name##2_crd [tbl_name##2_pos [tbl_name##1_pos [1]] - 1] =          \
        atoi(argv[1]);                                                     \
    tbl_name##_vals[tbl_name##2_pos [tbl_name##1_pos [1]] - 1] +=          \
        atof(argv[2]);                                                     \
                                                                           \
    return 0;                                                              \
  }

// this is the "dsTbl2" type, aka "csr" but without values
#define GEN_DSTBL2(tbl_name)                                                   \
  static int tbl_name##_i1_ = 0;                                               \
  static int gen_##tbl_name##_callback(void* data, int argc, char** argv,      \
                                       char** azColName) {                     \
    while (tbl_name##_i1_ <= atoi(argv[0])) {                                  \
      tbl_name##2_pos [tbl_name##_i1_ + 1] = tbl_name##2_pos [tbl_name##_i1_]; \
      tbl_name##_i1_ += 1;                                                     \
    }                                                                          \
    if (tbl_name##2_pos [atoi(argv[0])] ==                                     \
            tbl_name##2_pos [atoi(argv[0]) + 1] ||                             \
        atoi(argv[1]) !=                                                       \
            tbl_name##2_crd [tbl_name##2_pos [atoi(argv[0]) + 1] - 1]) {       \
      tbl_name##2_pos [atoi(argv[0]) + 1] += 1;                                \
    }                                                                          \
    tbl_name##2_crd [tbl_name##2_pos [atoi(argv[0]) + 1] - 1] = atoi(argv[1]); \
                                                                               \
    return 0;                                                                  \
  }

// this is the "ssTbl2" type, aka "dcsr" but without values
#define GEN_SSTBL2(tbl_name)                                               \
  static int gen_##tbl_name##_callback(void* data, int argc, char** argv,  \
                                       char** azColName) {                 \
    if (tbl_name##1_pos [0] == tbl_name##1_pos [1] ||                      \
        atoi(argv[0]) != tbl_name##1_crd [tbl_name##1_pos [1] - 1]) {      \
      tbl_name##1_pos [1] = (tbl_name##1_pos [1] + 1);                     \
      tbl_name##2_pos [((tbl_name##1_pos [1] - 1) + 1)] =                  \
          tbl_name##2_pos [(tbl_name##1_pos [1] - 1)];                     \
    }                                                                      \
    tbl_name##1_crd [tbl_name##1_pos [1] - 1] = atoi(argv[0]);             \
                                                                           \
    if (tbl_name##2_pos [tbl_name##1_pos [1] - 1] ==                       \
            tbl_name##2_pos [tbl_name##1_pos [1]] ||                       \
        atoi(argv[1]) !=                                                   \
            tbl_name##2_crd [tbl_name##2_pos [tbl_name##1_pos [1]] - 1]) { \
      tbl_name##2_pos [tbl_name##1_pos [1]] += 1;                          \
    }                                                                      \
                                                                           \
    tbl_name##2_crd [tbl_name##2_pos [tbl_name##1_pos [1]] - 1] =          \
        atoi(argv[1]);                                                     \
                                                                           \
    return 0;                                                              \
  }

GEN_MAT(tpch_lineitem)
GEN_DSTBL2(tpch_customer)
GEN_SSTBL2(tpch_orders)
GEN_SSTBL2(tpch_supplier)
GEN_DSTBL2(tpch_nation)

static int gen_ASIA_callback(void* data,
                             int argc,
                             char** argv,
                             char** azColName) {
  ASIA = atoi(argv[0]);
  return 0;
}

namespace {

int populate_tpch(sqlite3* db) {
  char* zErrMsg;
  int rc;
  void* data = nullptr;

#define GET_MAT(tbl_name, col1, col2, col3)                                  \
  rc = sqlite3_exec(db,                                                      \
                    "SELECT " #col1 ", " #col2 ", " #col3 " FROM " #tbl_name \
                    " ORDER BY " #col1 ", " #col2 "",           \
                    gen_tpch_##tbl_name##_callback, (void*)data, &zErrMsg);  \
  if (rc != SQLITE_OK) {                                                     \
    printf("%s:%d: %s\n", __FILE__, __LINE__, zErrMsg);                      \
    return rc;                                                               \
  }

#define GET_TBL2(tbl_name, col1, col2)                                      \
  rc = sqlite3_exec(db,                                                     \
                    "SELECT " #col1 ", " #col2 " FROM " #tbl_name           \
                    " ORDER BY " #col1 ", " #col2,                          \
                    gen_tpch_##tbl_name##_callback, (void*)data, &zErrMsg); \
  if (rc != SQLITE_OK) {                                                    \
    printf("%s:%d: %s\n", __FILE__, __LINE__, zErrMsg);                     \
    return rc;                                                              \
  }

  rc = sqlite3_exec(db, "SELECT r_regionkey FROM region WHERE r_name = 'ASIA'",
                    gen_ASIA_callback, (void*)data, &zErrMsg);
  if (rc != SQLITE_OK) {
    printf("%s:%d: %s\n", __FILE__, __LINE__, zErrMsg);
    return rc;
  }

  printf("ASIA = %d\n", ASIA);

  GET_MAT(lineitem, l_orderkey, l_suppkey, l_extendedprice * (1 - l_discount))
  GET_TBL2(customer, c_custkey, c_nationkey)
  GET_TBL2(orders, o_custkey, o_orderkey)
  GET_TBL2(supplier, s_nationkey, s_suppkey)
  GET_TBL2(nation, n_nationkey, n_regionkey)

  return rc;
}
}  // namespace
