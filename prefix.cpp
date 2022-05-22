#include "stdio.h"
#include "stdlib.h"
#include "stdbool.h"
#include <vector>
#include <cassert>

#include <string>
#include <iostream>
#include <fstream>
#include <sstream>
#include <filesystem>
#define num double
#define index int
#define BUFFER_SIZE 10

using namespace std;

index min(index a, index b) {
  return (a < b) ? a : b;
}

index foo;

template <typename T>
class Iter {
  public:
  virtual bool done() = 0;
  virtual void next() = 0;
  virtual index current() = 0;
  virtual T& value() = 0;
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

  bool done() override {
    //printf("done. i: %i, length: %i\n", this->i, this->length);
    return i >= length;
  }
  void next() override {
    //printf("next. i: %i\n", this->i);
    i++;
  }
  index current() override { return this->i; }
  T& value() override {
    //printf("value. i: %i\n", this->i);
    return values[i];
  }
  void reset() override {
    //printf("reset. i: %i\n", this->i);
    this->i = 0;
  }
  void finish() override { i = length; }
  void skip(index j) override { i = j; }
};

template <typename T>
class SparseArray : public Array<T> {
  public:
  std::vector<index> indices;

  index current() override {
    return this->indices[this->i];
  }
  void skip(index j) override {
    while (this->i < this->length && indices[this->i] < j) this->i++;
  }
  // helpers for loading
  void push(index j) {
    assert(this->length == 0 || j >= this->current());
    if (this->length == 0 || j != this->current()) {
      this->indices.push_back(j);
      this->values.emplace_back();
      this->i = this->length++;
    }
  }
  void terminate(index max) {
    this->indices.push_back(max);
    this->values.emplace_back();
  }
  T* value_ref() {
    return &this->values.at(this->i);
  }
};

template <typename T>
class SparseStorageArray : public SparseArray<T> {
  public:

  bool done() override { return false; }
  void skip(index j) override {
    //cout << "skipping: " << j << endl;
    if (!(this->length == 0 || j >= this->current())) {
      cout << "l: " << this->length << " j: " << j << " cur: " << this->current() << endl;
      assert(false);
    }
    if (this->length == 0 || j != this->current()) {
      this->indices.push_back(j);
      this->values.emplace_back();
      this->i = this->indices.size() - 1;
      this->length = this->indices.size();
    }
  }
  T* value_ref() {
    return &this->values.at(this->i);
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
  cout << "printing array. len: " << x.length << endl;;
  for (int i = 0; i < x.length; i++) {
    printf("(i: %d, v: %f)", x.indices[i], x.values[i]);
  }
  printf("\n");
}
void printMat(SparseArray<SparseArray<num>> x) {
  for (int i = 0; i < x.length; i++) {
    printArray(x.values[i]);
  }
  printf("\n");
}

void printArray_(SparseStorageArray<num> x) {
  cout << "printing array_. len: " << x.length << endl;;
  for (int i = 0; i < x.length; i++) {
    //if (abs(x.values[i]) > 0.0000001)
    printf("(i: %d, v: %f)", x.indices[i], x.values[i]);
  }
  printf("\n");
}
void printMat_(SparseStorageArray<SparseStorageArray<num>> x) {
  for (int i = 0; i < x.length; i++) {
    printArray_(x.values[i]);
  }
  printf("\n");
}

std::vector<std::string> split(const std::string &s, char delim) {
  std::stringstream ss(s);
  std::string item;
  std::vector<std::string> elems;
  while (std::getline(ss, item, delim)) {
    if (item.length() > 0) {
      elems.push_back(item);
    }
  }
  return elems;
}

// dense
SparseArray<num> loadvec(string name) {
  ifstream file(name);
  if (file.fail()) {
    throw runtime_error("file doesn't exist");
  }
  string line;
  SparseArray<num> result;
  int skip = 1;
  index i = 1;
  while(getline(file, line)) {
    auto elems = split(line, ' ');
    if (elems.size() > 0) {
      if (elems[0][0] == '%') continue;
      if (skip-- > 0) {continue;}
      {
	num val = atof(elems[0].c_str());
	result.push(i++);
	result.value() += val;
      }
    }
  }
  result.terminate(i);

  result.reset();
  printf("loadvec:\n");
  printArray(result);
  return result;
}

SparseArray<SparseArray<num>> loadmtx(string name) {
  ifstream file(name);
  if (file.fail()) {
    throw runtime_error("file doesn't exist");
  }
  string line;
  SparseArray<SparseArray<num>> result;
  int skip = 1;
  int i_max, j_max;
  while(getline(file, line)) {
    auto elems = split(line, ' ');
    if (elems.size() > 0) {
      if (elems[0][0] == '%') continue;
      if (skip-- > 0) {
	i_max = atoi(elems[1].c_str())+1;
	j_max = atoi(elems[0].c_str())+1;
	continue;
      }
      {
	index i = atoi(elems[1].c_str());
	index j = atoi(elems[0].c_str());
	num val = atof(elems[2].c_str());
	if (result.length > 0 && i != result.current()) {
	  result.value().terminate(j_max);
	  result.value().reset();
	}
	result.push(i);
	(*result.value_ref()).push(j);
	*(*result.value_ref()).value_ref() += val;
      }
    }
  }
  result.value().terminate(j_max);
  result.value().reset();
  result.terminate(i_max);
  //result.value().terminate(j_max);
  result.reset();
  printf("loadmtx:\n");
  //printMat(result);
  return result;
}

int main() {
  int __i = 0;

  //auto m = loadmtx("cavity11/cavity11.mtx");
  //auto m = loadmtx("test.mtx");
  //printMat(m);

// (sic)
