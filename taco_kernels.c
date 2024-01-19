
double taco_sum_mul2() {
load_ssA();
load_ssB();
#include "taco/sum_mul2.c"
}
double taco_sum_add2() {
load_ssA();
load_ssB();
#include "taco/sum_add2.c"
}
double taco_sum_mul2_csr() {
load_ssA();
load_dsB();
#include "taco/sum_mul2_csr.c"
}
double taco_inner2ss() {
load_ssA();
load_ssB();
#include "taco/inner2ss.c"
}

double taco_wcoj() {
load_ssR();
load_ssT();
#include "taco/wcoj.c"
}

double taco_mttkrp() {
load_dsA();
load_dsB();
load_sssC();
  //printf("TODO\n");
#include "taco/mttkrp.c"
  return 0;
}
double taco_sum_mul2_inner() {
load_ssA();
load_ssB();
load_dsA();
load_dsB();
#include "taco/sum_mul2_inner.c"
}
double taco_sum_mul2_inner_ss() {
load_ssA();
load_ssB();
#include "taco/sum_mul2_inner_ss.c"
}
double taco_spmv() {
load_ssA();
load_dV();
#include "taco/spmv.c"
}
double taco_filter_spmv() {
//load_sV();
//load_dsA();
//#include "taco/spmv.c"
return 0.0;
}
/* here end */

