
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
      for (int32_t jA = A2_pos[iA]; jA < A2_pos[(iA + 1)]; jA++) {
        for (int32_t kB = B2_pos[iB]; kB < B2_pos[(iB + 1)]; kB++) {
          out_val += A_vals[jA] * B_vals[kB];
        }
      }
    }
    iA += (int32_t)(iA0 == i);
    iB += (int32_t)(iB0 == i);
  }

  return out_val;

