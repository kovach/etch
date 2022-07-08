using namespace std;

#define TACO_MIN min

void taco_ijk_sum()
{
  // cout << "taco_ijk_sum" << endl;
  auto t1 = std::chrono::high_resolution_clock::now();
  out_val = 0;
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
          out_val += A_vals[jA] * B_vals[kB];
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

  // cout << "taco iterations: " << _i << endl;

  // cout << "out: " << out << "(<- IGNORE)" << endl;
  //   auto t2 = std::chrono::high_resolution_clock::now();
  //   std::cout << "took: "
  //             << std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1)
  //                    .count()
  //             << std::endl;
}

void taco_ttv() {
  out_val = 0;
  auto t1 = std::chrono::high_resolution_clock::now();
  for (int32_t iC = C1_pos[0]; iC < C1_pos[1]; iC++) {
    for (int32_t jC = C2_pos[iC]; jC < C2_pos[(iC + 1)]; jC++) {
      int32_t kC = C3_pos[jC];
      int32_t pC3_end = C3_pos[(jC + 1)];
      int32_t kV = V1_pos[0];
      int32_t pV1_end = V1_pos[1];

      while (kC < pC3_end && kV < pV1_end) {
        int32_t kC0 = C3_crd[kC];
        int32_t kV0 = V1_crd[kV];
        int32_t k = TACO_MIN(kC0,kV0);
        if (kC0 == k && kV0 == k) {
          out_val += C_vals[kC] * V_vals[kV];
        }
        kC += (int32_t)(kC0 == k);
        kV += (int32_t)(kV0 == k);
      }
    }
  }


  // std::cout << "out: " << out << endl;
  //   auto t2 = std::chrono::high_resolution_clock::now();
  //   std::cout << "taco took: "
  //             << std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1)
  //                    .count()
  //             << std::endl;

}
