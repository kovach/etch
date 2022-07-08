#include "stdio.h"
#include "stdlib.h"
#include "stdbool.h"
#include <vector>
#include <cassert>
#include <chrono>
#include <string>
#include <cstring>
#include <iostream>
#include <fstream>
#include <sstream>
#include <filesystem>
#include <map>
#include <algorithm>

#define num double
#define index int
// #define BUFFER_SIZE 10

// todo
int array_size = 1000000;
int out1_i = -1;
int out2_i = -1;

int V1_i = -1;
index* V1_crd = (index*)calloc(array_size, sizeof(index));
index* V1_pos = (index*)calloc(array_size, sizeof(index));
num* V_vals = (num*)calloc(array_size, sizeof(num));

int A1_i = -1;
int A2_i = -1;
index _A = 0;
index* A1_crd = (index*)calloc(array_size, sizeof(index));
index* A1_pos = (index*)calloc(array_size, sizeof(index));
index* A2_crd = (index*)calloc(array_size, sizeof(index));
index* A2_pos = (index*)calloc(array_size, sizeof(index));
num* A_vals = (num*)calloc(array_size, sizeof(num));

int M1_i = -1;
int M2_i = -1;
index _M = 0;
index* M1_crd = (index*)calloc(array_size, sizeof(index));
index* M1_pos = (index*)calloc(array_size, sizeof(index));
index* M2_crd = (index*)calloc(array_size, sizeof(index));
index* M2_pos = (index*)calloc(array_size, sizeof(index));
num* M_vals = (num*)calloc(array_size, sizeof(num));

int C1_i = -1;
int C2_i = -1;
int C3_i = -1;
index _C = 0;
index* C1_crd = (index*)calloc(array_size, sizeof(index));
index* C1_pos = (index*)calloc(array_size, sizeof(index));
index* C2_crd = (index*)calloc(array_size, sizeof(index));
index* C2_pos = (index*)calloc(array_size, sizeof(index));
index* C3_crd = (index*)calloc(array_size, sizeof(index));
index* C3_pos = (index*)calloc(array_size, sizeof(index));
num* C_vals = (num*)calloc(array_size, sizeof(num));

int D1_i = -1;
int D2_i = -1;
int D3_i = -1;
index _D = 0;
index* D1_crd = (index*)calloc(array_size, sizeof(index));
index* D1_pos = (index*)calloc(array_size, sizeof(index));
index* D2_crd = (index*)calloc(array_size, sizeof(index));
index* D2_pos = (index*)calloc(array_size, sizeof(index));
index* D3_crd = (index*)calloc(array_size, sizeof(index));
index* D3_pos = (index*)calloc(array_size, sizeof(index));
num* D_vals = (num*)calloc(array_size, sizeof(num));

int B1_i = -1;
int B2_i = -1;
index* B1_crd = (index*)calloc(array_size, sizeof(index));
index* B1_pos = (index*)calloc(array_size, sizeof(index));
index* B2_crd = (index*)calloc(array_size, sizeof(index));
index* B2_pos = (index*)calloc(array_size, sizeof(index));
index* out1_crd = (index*)calloc(array_size, sizeof(index));
index* out1_pos = (index*)calloc(array_size, sizeof(index));
index* out2_crd = (index*)calloc(array_size*10, sizeof(index));
index* out2_pos = (index*)calloc(array_size, sizeof(index));
index* out0_crd = (index*)calloc(array_size, sizeof(index));
num* out_vals = (num*)calloc(array_size*10, sizeof(num));
num* B_vals = (num*)calloc(array_size, sizeof(num));
num out = 0.0;
num out_val = 0.0;

//index* A0_crd = (index*)calloc(array_size, sizeof(index));
//index* B0_crd = (index*)calloc(array_size, sizeof(index));
// index iA = 0;
// index jA = 0;
// index iB = 0;
// index jB = 0;
// index _B = 0;
// index _out = 0;
index iout = 0;
index jout = 0;

#include "taco_kernels.cpp"
#include "ttv.cpp"
#include "ttm.cpp"
#include "mttkrp.cpp"
#include "inner3.cpp"
#include "mmul2.cpp"


using namespace std;

index min(index a, index b) {
  return (a < b) ? a : b;
}
index max(index a, index b) {
  return (a > b) ? a : b;
}

bool int_lt(index a, index b) {
  return a < b;
}
bool int_eq(index a, index b) {
  return a == b;
}


// todo optimize
bool str_lt(char* a, char* b) {
  return strcmp(a,b) < 0;
}
bool str_eq(char* a, char* b) {
  return strcmp(a,b) == 0;
}

bool file_empty(std::ifstream& pFile)
{
    return pFile.peek() == std::ifstream::traits_type::eof();
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

class Vector {
  public:
  map<tuple<index>, num> data;
  int i_max;
  Vector(int i_max, map<tuple<index>, num> data) : i_max(i_max), data(data) {
  }
};

class Matrix {
  public:
  map<tuple<index, index>, num> data;
  int i_max, j_max;
  Matrix(int i_max, int j_max, map<tuple<index, index>, num> data) : i_max(i_max), j_max(j_max), data(data) {
  }
};

class Cube {
  public:
  map<tuple<index, index, index>, num> data;
  int i_max, j_max, k_max;
  Cube(int i_max, int j_max, int k_max, map<tuple<index, index, index>, num> data) : i_max(i_max), j_max(j_max), k_max(k_max), data(data) {
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

Cube load_random(int rows, int columns, int ranks, int n) {
  map<tuple<index, index, index>, num> result;
  int count = 0;
  for (int i = 0; i < rows; i++) {
    for (int j = 0; j < columns; j++) {
      for (int k = 0; k < ranks; k++) {
	if (std::rand() % n == 0) {
	  float r = static_cast <float> (rand()) / static_cast <float> (RAND_MAX);
	  result[make_tuple(i,j,k)] = r - 0.5;
	  count++;
	}
      }
    }
  }
  cout << "nnz: " << count << endl;
  return Cube(rows, columns, ranks, result);
}

Matrix load_random(int rows, int columns, int n) {
  map<tuple<index, index>, num> result;
  int count = 0;
  for (int i = 0; i < rows; i++) {
    for (int j = 0; j < columns; j++) {
      if (std::rand() % n == 0) {
	float r = static_cast <float> (rand()) / static_cast <float> (RAND_MAX);
	result[make_tuple(i,j)] = r - 0.5;
	count++;
      }
    }
  }
  cout << "nnz: " << count << endl;
  return Matrix(rows, columns, result);
}

Vector load_random(int rows, int n) {
  map<tuple<index>, num> result;
  int count = 0;
  for (int i = 0; i < rows; i++) {
      if (std::rand() % n == 0) {
	float r = static_cast <float> (rand()) / static_cast <float> (RAND_MAX);
	result[make_tuple(i)] = r - 0.5;
	count++;
      }
  }
  cout << "nnz: " << count << endl;
  return Vector(rows, result);
}


int main() {
  int __i = 0;
  cout << "starting..." << endl;

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
  //auto x = loadmtx1("data/cavity11.mtx");
  //auto y = loadmtx1("data/cavity11.mtx");
  int m = 2000;
  int k = 2000;
  int l = 1000;
  Matrix x = load_random(m,k,40);
  Matrix y = load_random(k,l,40);
  Vector v = load_random(1000, 2);
  Cube c = load_random(100,100,1000, 20);
  //auto z = load_random(m,l, 20);
  //auto t1 = std::chrono::high_resolution_clock::now();
