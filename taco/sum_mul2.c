
  double out_val = 0.0;

  for (int32_t iA = A1_pos[0]; iA < A1_pos[1]; iA++) {
    int32_t jA = A2_pos[iA];
    int32_t pA2_end = A2_pos[(iA + 1)];
    int32_t jB = B1_pos[0];
    int32_t pB1_end = B1_pos[1];

    while (jA < pA2_end && jB < pB1_end) {
      int32_t jA0 = A2_crd[jA];
      int32_t jB0 = B1_crd[jB];
      int32_t j = TACO_MIN(jA0,jB0);
      if (jA0 == j && jB0 == j) {
        for (int32_t kB = B2_pos[jB]; kB < B2_pos[(jB + 1)]; kB++) {
          out_val += A_vals[jA] * B_vals[kB];
        }
      }
      jA += (int32_t)(jA0 == j);
      jB += (int32_t)(jB0 == j);
    }
  }

  return out_val;
