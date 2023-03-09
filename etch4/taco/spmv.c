
  double out_val = 0.0;

  for (int32_t iA = A1_pos[0]; iA < A1_pos[1]; iA++) {
    for (int32_t jA = A2_pos[iA]; jA < A2_pos[(iA + 1)]; jA++) {
      int32_t j = A2_crd[jA];
      out_val += A_vals[jA] * V_vals[j];
    }
  }

  return out_val;
