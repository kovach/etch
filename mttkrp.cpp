// Generated by the Tensor Algebra Compiler (tensor-compiler.org)

int mttkrp_compute() {
  out_val = 0.0;

  for (int32_t iC = C1_pos[0]; iC < C1_pos[1]; iC++) {
    int32_t jC = C2_pos[iC];
    int32_t pC2_end = C2_pos[(iC + 1)];
    int32_t jA = A1_pos[0];
    int32_t pA1_end = A1_pos[1];

    while (jC < pC2_end && jA < pA1_end) {
      int32_t jC0 = C2_crd[jC];
      int32_t jA0 = A1_crd[jA];
      int32_t j = TACO_MIN(jC0,jA0);
      if (jC0 == j && jA0 == j) {
        int32_t kC = C3_pos[jC];
        int32_t pC3_end = C3_pos[(jC + 1)];
        int32_t kB = B1_pos[0];
        int32_t pB1_end = B1_pos[1];

        while (kC < pC3_end && kB < pB1_end) {
          int32_t kC0 = C3_crd[kC];
          int32_t kB0 = B1_crd[kB];
          int32_t k = TACO_MIN(kC0,kB0);
          if (kC0 == k && kB0 == k) {
            int32_t lA = A2_pos[jA];
            int32_t pA2_end = A2_pos[(jA + 1)];
            int32_t lB = B2_pos[kB];
            int32_t pB2_end = B2_pos[(kB + 1)];

            while (lA < pA2_end && lB < pB2_end) {
              int32_t lA0 = A2_crd[lA];
              int32_t lB0 = B2_crd[lB];
              int32_t l = TACO_MIN(lA0,lB0);
              if (lA0 == l && lB0 == l) {
                out_val += (C_vals[kC] * A_vals[lA]) * B_vals[lB];
              }
              lA += (int32_t)(lA0 == l);
              lB += (int32_t)(lB0 == l);
            }
          }
          kC += (int32_t)(kC0 == k);
          kB += (int32_t)(kB0 == k);
        }
      }
      jC += (int32_t)(jC0 == j);
      jA += (int32_t)(jA0 == j);
    }
  }

  out_vals[0] = out_val;
  return 0;
}
