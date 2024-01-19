
  double out_val = 0.0;

  for (int32_t iC = C1_pos[0]; iC < C1_pos[1]; iC++) {
    for (int32_t jC = C2_pos[iC]; jC < C2_pos[(iC + 1)]; jC++) {
      int32_t j = C2_crd[jC];
      for (int32_t kC = C3_pos[jC]; kC < C3_pos[(jC + 1)]; kC++) {
        int32_t k = C3_crd[kC];
        int32_t lA = A2_pos[j];
        int32_t pA2_end = A2_pos[(j + 1)];
        int32_t lB = B2_pos[k];
        int32_t pB2_end = B2_pos[(k + 1)];

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
    }
  }

  return out_val;

