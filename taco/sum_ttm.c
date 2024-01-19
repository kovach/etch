
  double out_val = 0.0;

  for (int32_t i = 0; i < C1_dimension; i++) {
    for (int32_t jC = C2_pos[i]; jC < C2_pos[(i + 1)]; jC++) {
      for (int32_t k = 0; k < B1_dimension; k++) {
        int32_t lC = C3_pos[jC];
        int32_t pC3_end = C3_pos[(jC + 1)];
        int32_t lB = B2_pos[k];
        int32_t pB2_end = B2_pos[(k + 1)];

        while (lC < pC3_end && lB < pB2_end) {
          int32_t lC0 = C3_crd[lC];
          int32_t lB0 = B2_crd[lB];
          int32_t l = TACO_MIN(lC0,lB0);
          if (lC0 == l && lB0 == l) {
            out_val += C_vals[lC] * B_vals[lB];
          }
          lC += (int32_t)(lC0 == l);
          lB += (int32_t)(lB0 == l);
        }
      }
    }
  }

  return out_val;
