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

// want parent methods
template <typename T>
SparseArray<T> toVal(SparseStorageArray<T>& v) {
  auto result = SparseArray<T>();
  result.length = v.length;
  result.indices = v.indices;
  result.values = v.values;
  return result;
}


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
  int __i = 0;

  //SparseStorageArray<double> out;
  //SparseStorageArray<SparseStorageArray<double>> out2;
  //SparseArray<double> t1;
// (sic)
