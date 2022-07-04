#include "stdio.h"
#include "stdlib.h"
#include "stdbool.h"
#include <vector>
#include <cassert>
#include <chrono>
#include <string>
#include <iostream>
#include <fstream>
#include <sstream>
#include <filesystem>
#include <map>
#include <algorithm>
#define num double
#define index int
#define BUFFER_SIZE 10

using namespace std;

index min(index a, index b) {
  return (a < b) ? a : b;
}

index max(index a, index b) {
  return (a > b) ? a : b;
}

#define TACO_MIN min

bool file_empty(std::ifstream& pFile)
{
    return pFile.peek() == std::ifstream::traits_type::eof();
}

template <typename T>
class Iter {
  public:
  virtual inline bool done() = 0;
  virtual inline void next() = 0;
  virtual inline index current() = 0;
  virtual inline T& value() = 0;
  virtual inline void reset() = 0;
  virtual inline void finish() = 0;
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


  inline bool done() override {
    //printf("done. i: %i, length: %i\n", this->i, this->length);
    return i >= length;
  }
  inline void next() override {
    //printf("next. i: %i\n", this->i);
    i++;
  }
  inline index current() override { return this->i; }
  inline T& value() override {
    //printf("value. i: %i\n", this->i);
    return values[i];
  }
  inline void reset() override {
    //printf("reset. i: %i\n", this->i);
    this->i = 0;
  }
  inline void finish() override { i = length; }
  inline void skip(index j) override { i = j; }
};

template <typename T>
class SparseArray : public Array<T> {
  public:
  std::vector<index> indices;

  inline index current() override {
    return this->indices[this->i];
  }
  inline void skip(index j) override {
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
  inline T* value_ref() {
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
    printf("i: %d | ", x.indices[i]);
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
  //printArray(result);
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
  printMat(result);
  return result;
}

class Matrix {
  public:
  map<tuple<index, index>, num> data;
  int i_max, j_max;
  Matrix(int i_max, int j_max, map<tuple<index, index>, num> data) : i_max(i_max), j_max(j_max), data(data) {
  }
};

Matrix loadmtx1(string name) {
  cout << "hmm\n";
  ifstream file(name);
  if (file.fail()) {
    throw runtime_error("file doesn't exist");
  }
  string line;
  map<tuple<index, index>, num> temp;
  SparseArray<SparseArray<num>> result;
  int skip = 1;
  int i_max, j_max;
  while(getline(file, line)) {
    auto elems = split(line, ' ');
    if (elems.size() > 0) {
      if (elems[0][0] == '%') continue;
      if (skip-- > 0) {
	i_max = atoi(elems[0].c_str())+1;
	j_max = atoi(elems[1].c_str())+1;
	continue;
      }
      {
	index i = atoi(elems[0].c_str());
	index j = atoi(elems[1].c_str());
	num val = atof(elems[2].c_str());
	temp[make_tuple(i,j)] = val;
      }
    }
  }
  return Matrix(i_max, j_max, temp);
}

SparseArray<SparseArray<num>> loadmtx2(string name) {
  Matrix temp = loadmtx1(name);
  SparseArray<SparseArray<num>> result;

  int i_max = temp.i_max;
  int j_max = temp.j_max;
  for (auto const& x : temp.data) {
    index i = get<0>(x.first) ;
    index j = get<1>(x.first) ;
    num val = x.second;
    if (result.length > 0 && i != result.current()) {
      result.value().terminate(j_max);
      result.value().reset();
    }
    result.push(i);
    (*result.value_ref()).push(j);
    *(*result.value_ref()).value_ref() += val;
    // cout << get<0>(x.first) << get<1>(x.first)
    // 	 << endl << x.second << endl;
  }
  result.value().terminate(j_max);
  result.value().reset();
  result.terminate(i_max);
  //result.value().terminate(j_max);
  result.reset();
  printf("loadmtx:\n");
  printMat(result);
  return result;
}

  int array_size = 1000000;
  int out1_i = -1;
  int out2_i = -1;
  int A1_i = -1;
  int A2_i = -1;
  int B1_i = -1;
  int B2_i = -1;
  index* A1_crd = (index*)calloc(array_size, sizeof(index));
  index* A1_pos = (index*)calloc(array_size, sizeof(index));
  index* A2_crd = (index*)calloc(array_size, sizeof(index));
  index* A2_pos = (index*)calloc(array_size, sizeof(index));
  index* B1_crd = (index*)calloc(array_size, sizeof(index));
  index* B1_pos = (index*)calloc(array_size, sizeof(index));
  index* B2_crd = (index*)calloc(array_size, sizeof(index));
  index* B2_pos = (index*)calloc(array_size, sizeof(index));
  index* out1_crd = (index*)calloc(array_size, sizeof(index));
  index* out1_pos = (index*)calloc(array_size, sizeof(index));
  index* out2_crd = (index*)calloc(array_size*10, sizeof(index));
  index* out2_pos = (index*)calloc(array_size, sizeof(index));
  index* out0_crd = (index*)calloc(array_size, sizeof(index));
  index* A0_crd = (index*)calloc(array_size, sizeof(index));
  index* B0_crd = (index*)calloc(array_size, sizeof(index));
  num* out_vals = (num*)calloc(array_size*10, sizeof(num));
  num* A_vals = (num*)calloc(array_size, sizeof(num));
  num* B_vals = (num*)calloc(array_size, sizeof(num));
  num out = 0.0;
  index iA = 0;
  index jA = 0;
  index iB = 0;
  index jB = 0;
  index _A = 0;
  index _B = 0;
  index _out = 0;
  index iout = 0;
  index jout = 0;

void taco_ijk_sum()
{
  cout << "taco_ijk_sum" << endl;
  auto t1 = std::chrono::high_resolution_clock::now();
  out = 0;
  for (int32_t iA = A1_pos[0]; iA < A1_pos[1]; iA++) {
    int32_t jA = A2_pos[iA];
    int32_t pA2_end = A2_pos[(iA + 1)];
    int32_t jB = B1_pos[0];
    int32_t pB1_end = B1_pos[1];

    while (jA < pA2_end && jB < pB1_end) {
      int32_t jA0 = A2_crd[jA];
      int32_t jB0 = B1_crd[jB];
      int32_t j = min(jA0,jB0);
      if (jA0 == j && jB0 == j) {
        for (int32_t kB = B2_pos[jB]; kB < B2_pos[(jB + 1)]; kB++) {
          out += A_vals[jA] * B_vals[kB];
        }
      }
      jA += (int32_t)(jA0 == j);
      jB += (int32_t)(jB0 == j);
    }
  }
  cout << "out_taco: " << out << endl;
    auto t2 = std::chrono::high_resolution_clock::now();
    std::cout << "taco took: "
              << std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1)
                     .count()
              << std::endl;
}

void taco_ikjk() {
  auto t1 = std::chrono::high_resolution_clock::now();
  int _i = 0;
  for (int32_t iA = A1_pos[0]; iA < A1_pos[1]; iA++) {
    int32_t i = A1_crd[iA];
    int32_t pout2_begin = jout;
    for (int32_t jB = B1_pos[0]; jB < B1_pos[1]; jB++) {
      int32_t j = B1_crd[jB];
      double tkout_val = 0.0;
      int32_t kA = A2_pos[iA];
      int32_t pA2_end = A2_pos[(iA + 1)];
      int32_t kB = B2_pos[jB];
      int32_t pB2_end = B2_pos[(jB + 1)];
      while (kA < pA2_end && kB < pB2_end) {
        int32_t kA0 = A2_crd[kA];
        int32_t kB0 = B2_crd[kB];
        int32_t k = TACO_MIN(kA0,kB0);
        if (kA0 == k && kB0 == k) {
          tkout_val += A_vals[kA] * B_vals[kB];
        }
        kA += (int32_t)(kA0 == k);
        kB += (int32_t)(kB0 == k);
      }
      _i++;
      out_vals[jout] = tkout_val;
      out2_crd[jout] = j;
      jout++;
    }

    out2_pos[iout + 1] = jout;
    if (pout2_begin < jout) {
      out1_crd[iout] = i;
      iout++;
    }
  }

  out1_pos[1] = iout;

  cout << "taco iterations: " << _i << endl;

  cout << "out_taco: " << out << endl;
    auto t2 = std::chrono::high_resolution_clock::now();
    std::cout << "taco took: "
              << std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1)
                     .count()
              << std::endl;
}

int main() {
  int __i = 0;

 // int myints[] = {1,3,4,5,8,22};
 // std::vector<int> v(myints,myints+9);
 // std::sort (v.begin(), v.end());

 // int target = 5;
 // std::cout << "looking for a " << target << endl;
 // auto lower = lower_bound(v.begin(), v.end(), target);

 // cout << "eh: " << *lower << endl;
 // cout << "ok: " << lower - v.begin() << endl;

 //auto m = loadmtx("cavity11/cavity11.mtx");
 //auto m = loadmtx("test.mtx");
 //printMat(m);

// (sic)

  //auto x = loadmtx1("data/smaller.mtx");
  auto x = loadmtx1("data/cavity11.mtx");
  //auto t1 = std::chrono::high_resolution_clock::now();
