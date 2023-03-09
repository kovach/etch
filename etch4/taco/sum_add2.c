
  double out_val = 0;

  for (int32_t i = 0; i < B1_dimension; i++) {

    int32_t jA = A2_pos[i];
    int32_t pA2_end = A2_pos[(i + 1)];
    int32_t jB = B2_pos[i];
    int32_t pB2_end = B2_pos[(i + 1)];

    while (jA < pA2_end && jB < pB2_end) {
      int32_t jA0 = A2_crd[jA];
      int32_t jB0 = B2_crd[jB];
      int32_t j = TACO_MIN(jA0,jB0);
      if (jA0 == j && jB0 == j) {
        out_val += A_vals[jA] + B_vals[jB];
      }
      else if (jA0 == j) {
        out_val += A_vals[jA];
      }
      else {
        out_val += B_vals[jB];
      }
      jA += (int32_t)(jA0 == j);
      jB += (int32_t)(jB0 == j);
    }
    while (jA < pA2_end) {
      int32_t j = A2_crd[jA];
      out_val += A_vals[jA];
      jA++;
    }
    while (jB < pB2_end) {
      int32_t j = B2_crd[jB];
      out_val += B_vals[jB];
      jB++;
    }

  }

  return out_val;
