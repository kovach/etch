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

Matrix load_random(int rows, int columns, int n) {
  map<tuple<index, index>, num> result;
  for (int i = 0; i < rows; i++) {
    for (int j = 0; j < rows; j++) {
      if (std::rand() % n == 0) {
	float r = static_cast <float> (rand()) / static_cast <float> (RAND_MAX);
	result[make_tuple(i,j)] = r - 0.5;
      }
    }
  }
  return Matrix(rows, columns, result);
}


int array_size = 1000000;
int out1_i = -1;
int out2_i = -1;

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

void taco_ijk_sum()
{
  // cout << "taco_ijk_sum" << endl;
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
  // cout << "out_taco: " << out << endl;
  //   auto t2 = std::chrono::high_resolution_clock::now();
  //   std::cout << "taco took: "
  //             << std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1)
  //                    .count()
  //             << std::endl;
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
  //auto x = loadmtx1("data/cavity11.mtx");
  auto x = load_random(1000,1000, 6);
  auto y = load_random(1000,1000, 5);
  auto z = load_random(1000,1000, 20);
  //auto t1 = std::chrono::high_resolution_clock::now();
