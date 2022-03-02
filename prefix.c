#include "stdio.h"
#include "stdlib.h"
#include "stdbool.h"
#include <vector>
#define num float
#define index int
#define BUFFER_SIZE 10
typedef struct {
  std::vector<index> is;
  std::vector<num>   vs;
} sparse_vec;

void put(num* x, int i, num value) {
  printf("put: %d, %f\n", i, (float)value);
  *(x + i) += value;
}
void put_sparse(sparse_vec x, int i, num value) {
  printf("put sparse: %d, %f\n", i, (float)value);
  x.is.push_back(i);
  x.vs.push_back(value);
}
int main() {

