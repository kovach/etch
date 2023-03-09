
  double out_val = 0.0;

  for (int32_t i = 0; i < D1_dimension; i++) {
    int32_t jC = C2_pos[i];
    int32_t pC2_end = C2_pos[(i + 1)];
    int32_t jD = D2_pos[i];
    int32_t pD2_end = D2_pos[(i + 1)];

    while (jC < pC2_end && jD < pD2_end) {
      int32_t jC0 = C2_crd[jC];
      int32_t jD0 = D2_crd[jD];
      int32_t j = TACO_MIN(jC0,jD0);
      if (jC0 == j && jD0 == j) {
        int32_t kC = C3_pos[jC];
        int32_t pC3_end = C3_pos[(jC + 1)];
        int32_t kD = D3_pos[jD];
        int32_t pD3_end = D3_pos[(jD + 1)];

        while (kC < pC3_end && kD < pD3_end) {
          int32_t kC0 = C3_crd[kC];
          int32_t kD0 = D3_crd[kD];
          int32_t k = TACO_MIN(kC0,kD0);
          if (kC0 == k && kD0 == k) {
            out_val += C_vals[kC] * D_vals[kD];
          }
          kC += (int32_t)(kC0 == k);
          kD += (int32_t)(kD0 == k);
        }
      }
      jC += (int32_t)(jC0 == j);
      jD += (int32_t)(jD0 == j);
    }
  }

  return out_val;
