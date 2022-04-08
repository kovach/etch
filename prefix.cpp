#include "stdio.h"
#include "stdlib.h"
#include "stdbool.h"
#include <vector>
#define num double
#define index int
#define BUFFER_SIZE 10

template <typename T>
struct node {
  int                length = 0;
  std::vector<index> indices;
  std::vector<T>     children;
};

void put(num* x, int i, num value) {
  // printf("put: %d, %f\n", i, (float)value);
  *(x + i) += value;
}

template <typename T>
void put_sparse(node<T> &x, int i, T value) {
  printf("put sparse: %d\n", i);
  x.indices.push_back(i);
  x.children.push_back(value);
  x.length++;
}

void put_debug(num* x, int i, num value) {
  printf("put: %d, %f\n", i, (float)value);
}

int main() {
  node<num> v;
  put_sparse(v, 1, -1.);
  //put_sparse(v, 2, 0.);
  // put_sparse(v, 3, 1.);
  node<node<num>> A, B;
  node<node<node<num>>> C, D;
  index iA, iB, jA, jB, kA, kB;
  put_sparse(A, 1, v);
  put_sparse(A, 2, v);
  put_sparse(B, 1, v);
  put_sparse(B, 2, v);
  int __i = 0;
// (sic)
