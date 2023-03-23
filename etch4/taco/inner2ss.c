
  double out_val = 0.0;

  int32_t iA = A1_pos[0];
  int32_t pA1_end = A1_pos[1];
  int32_t iB = B1_pos[0];
  int32_t pB1_end = B1_pos[1];

  while (iA < pA1_end && iB < pB1_end) {
    int32_t iA0 = A1_crd[iA];
    int32_t iB0 = B1_crd[iB];
    int32_t i = TACO_MIN(iA0,iB0);

    if (iA0 == i && iB0 == i) {
      int32_t jA = A2_pos[iA];
      int32_t pA2_end = A2_pos[(iA + 1)];
      int32_t jB = B2_pos[iB];
      int32_t pB2_end = B2_pos[(iB + 1)];

      while (jA < pA2_end && jB < pB2_end) {
        int32_t jA0 = A2_crd[jA];
        int32_t jB0 = B2_crd[jB];
        int32_t j = TACO_MIN(jA0,jB0);
        if (jA0 == j && jB0 == j) {
          out_val += A_vals[jA] * B_vals[jB];
        }
        jA += (int32_t)(jA0 == j);
        jB += (int32_t)(jB0 == j);
      }
    }
    iA += (int32_t)(iA0 == i);
    iB += (int32_t)(iB0 == i);
  }

  return out_val;

