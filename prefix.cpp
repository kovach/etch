#include "stdio.h"
#include "stdlib.h"
#include "stdbool.h"
#include <vector>
#include <cassert>
#define num double
#define index int
#define BUFFER_SIZE 10

template <typename T>
class Iter {
  public:
  virtual bool done() = 0;
  virtual void next() = 0;
  virtual index current() = 0;
  virtual T value() = 0;
  virtual void reset() = 0;
  virtual void finish() = 0;
};

template <typename T>
class Skippable : public Iter<T> {
  public:
  virtual void skip(index i) = 0;
};

template <typename T>
class Array : public Skippable<T> {
  public:
  index i = 0;
  int length = 0;
  std::vector<T> values;
  public:
  bool done() override {
    return i >= length;
  }
  void next() override { i++; }
  index current() override { return i; }
  T value() override { return values[i]; }
  void reset() override { i = 0; }
  void finish() override { i = length; }
  void skip(index j) override { i = j; }
};

template <typename T>
class SparseArray : public Array<T> {
  public:
  std::vector<index> indices;

  public:
  index current() override {
    return indices[this->i];
  }
  void skip(index j) override {
    while (this->i < this->length && indices[this->i] < j) this->i++;
  }
};

class SparseVec : public SparseArray<num> {};

template <typename T>
class SparseStorageArray : public SparseArray<T> {
  public:
  index i = 0;
  int length = 0;
  std::vector<T> values;
  public:
  bool done() override { return false; }
  T* value_ref() {
    return &this->values.at(this->i);
  }
  void skip(index j) override {
    assert(this->length == 0 || j >= this->current());
    if (this->length == 0 || j != this->current()) {
      this->indices.push_back(j);
      //this->values.push_back(T());
      this->values.emplace_back();
      this->i = this->length;
      this->length++;
    }
  }
};

template <typename T>
SparseArray<T>* toVal(SparseStorageArray<T>& v) {
  auto result = new SparseArray<T>();
  result->length = v.length;
  result->indices = v.indices;
  result->values = v.values;
  return result;
}


// template <class T>
// class Acc {
//   void put(T);
// };
// class Node {
//   Node* empty();
// };
// template <class T>
// class LeafNode : Node {
//   LeafNode<T>* empty() {
//     return new LeafNode();
//   }
//   std::vector<index> indices;
//   std::vector<num> children;
// };

// template <class T>
// class InnerNode : Node {
//   int length = 0;
//   std::vector<index> indices;
//   std::vector<> children;

//   InnerNode* empty() {
//     return new InnerNode();
//   }
//   put(index i) {
//     if (length == 0 || indices[length-1] != i) {
//       indices.push_back(i);
//       children.push_back(
// };

void put_debug(num* x, int i, num value) {
  printf("put: %d, %f\n", i, (float)value);
}

void printArray(SparseArray<num> x) {
  for (int i = 0; i < x.length; i++) {
    printf("(i: %d, v: %f)", x.indices[i], x.values[i]);
  }
  printf("\n");
}

void printArray_(SparseStorageArray<num> x) {
  for (int i = 0; i < x.length; i++) {
    printf("(i: %d, v: %f)", x.indices[i], x.values[i]);
  }
  printf("\n");
}

int main() {
  index iA, iB, jA, jB, kA, kB;
  // index i;
  // index* i = (index *) malloc(10 * sizeof(index));
  int __i = 0;
  // double acc0 = 0;

  SparseStorageArray<double> out;
  SparseStorageArray<double> out1;
  SparseStorageArray<double> out1_;
  SparseStorageArray<SparseStorageArray<double>> out2;
  SparseArray<double> t1;
  SparseArray<double> t2;
// (sic)
