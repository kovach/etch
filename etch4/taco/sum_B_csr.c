
  double out_val = 0.0;

  for (int32_t i = 0; i < B1_dimension; i++) {
    for (int32_t jB = B2_pos[i]; jB < B2_pos[(i + 1)]; jB++) {
      out_val += B_vals[jB];
    }
  }

  return out_val;
