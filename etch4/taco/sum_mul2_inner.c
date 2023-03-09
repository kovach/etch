
  double out_val = 0.0;

  for (int32_t i = 0; i < A1_dimension; i++) {
    for (int32_t j = 0; j < B1_dimension; j++) {
      int32_t kA = A2_pos[i];
      int32_t pA2_end = A2_pos[(i + 1)];
      int32_t kB = B2_pos[j];
      int32_t pB2_end = B2_pos[(j + 1)];

      while (kA < pA2_end && kB < pB2_end) {
        int32_t kA0 = A2_crd[kA];
        int32_t kB0 = B2_crd[kB];
        int32_t k = TACO_MIN(kA0,kB0);
        if (kA0 == k && kB0 == k) {
          out_val += A_vals[kA] * B_vals[kB];
        }
        kA += (int32_t)(kA0 == k);
        kB += (int32_t)(kB0 == k);
      }
    }
  }

  return out_val;
