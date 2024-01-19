
int evaluate(taco_tensor_t *out, taco_tensor_t *A, taco_tensor_t *B) {
  int out1_dimension = (int)(out->dimensions[0]);
  int* restrict out2_pos = (int*)(out->indices[1][0]);
  int* restrict out2_crd = (int*)(out->indices[1][1]);
  double* restrict out_vals = (double*)(out->vals);
  int A1_dimension = (int)(A->dimensions[0]);
  int* restrict A2_pos = (int*)(A->indices[1][0]);
  int* restrict A2_crd = (int*)(A->indices[1][1]);
  double* restrict A_vals = (double*)(A->vals);
  int B1_dimension = (int)(B->dimensions[0]);
  int* restrict B2_pos = (int*)(B->indices[1][0]);
  int* restrict B2_crd = (int*)(B->indices[1][1]);
  double* restrict B_vals = (double*)(B->vals);

  out2_pos = (int32_t*)malloc(sizeof(int32_t) * (out1_dimension + 1));
  out2_pos[0] = 0;
  for (int32_t pout2 = 1; pout2 < (out1_dimension + 1); pout2++) {
    out2_pos[pout2] = 0;
  }
  int32_t out2_crd_size = 1048576;
  out2_crd = (int32_t*)malloc(sizeof(int32_t) * out2_crd_size);
  int32_t jout = 0;
  int32_t out_capacity = 1048576;
  out_vals = (double*)malloc(sizeof(double) * out_capacity);

  for (int32_t i = 0; i < B1_dimension; i++) {
    int32_t pout2_begin = jout;

    int32_t jA = A2_pos[i];
    int32_t pA2_end = A2_pos[(i + 1)];
    int32_t jB = B2_pos[i];
    int32_t pB2_end = B2_pos[(i + 1)];

    while (jA < pA2_end && jB < pB2_end) {
      int32_t jA0 = A2_crd[jA];
      int32_t jB0 = B2_crd[jB];
      int32_t j = TACO_MIN(jA0,jB0);
      if (jA0 == j && jB0 == j) {
        if (out_capacity <= jout) {
          out_vals = (double*)realloc(out_vals, sizeof(double) * (out_capacity * 2));
          out_capacity *= 2;
        }
        out_vals[jout] = A_vals[jA] + B_vals[jB];
        if (out2_crd_size <= jout) {
          out2_crd = (int32_t*)realloc(out2_crd, sizeof(int32_t) * (out2_crd_size * 2));
          out2_crd_size *= 2;
        }
        out2_crd[jout] = j;
        jout++;
      }
      else if (jA0 == j) {
        if (out_capacity <= jout) {
          out_vals = (double*)realloc(out_vals, sizeof(double) * (out_capacity * 2));
          out_capacity *= 2;
        }
        out_vals[jout] = A_vals[jA];
        if (out2_crd_size <= jout) {
          out2_crd = (int32_t*)realloc(out2_crd, sizeof(int32_t) * (out2_crd_size * 2));
          out2_crd_size *= 2;
        }
        out2_crd[jout] = j;
        jout++;
      }
      else {
        if (out_capacity <= jout) {
          out_vals = (double*)realloc(out_vals, sizeof(double) * (out_capacity * 2));
          out_capacity *= 2;
        }
        out_vals[jout] = B_vals[jB];
        if (out2_crd_size <= jout) {
          out2_crd = (int32_t*)realloc(out2_crd, sizeof(int32_t) * (out2_crd_size * 2));
          out2_crd_size *= 2;
        }
        out2_crd[jout] = j;
        jout++;
      }
      jA += (int32_t)(jA0 == j);
      jB += (int32_t)(jB0 == j);
    }
    while (jA < pA2_end) {
      int32_t j = A2_crd[jA];
      if (out_capacity <= jout) {
        out_vals = (double*)realloc(out_vals, sizeof(double) * (out_capacity * 2));
        out_capacity *= 2;
      }
      out_vals[jout] = A_vals[jA];
      if (out2_crd_size <= jout) {
        out2_crd = (int32_t*)realloc(out2_crd, sizeof(int32_t) * (out2_crd_size * 2));
        out2_crd_size *= 2;
      }
      out2_crd[jout] = j;
      jout++;
      jA++;
    }
    while (jB < pB2_end) {
      int32_t j = B2_crd[jB];
      if (out_capacity <= jout) {
        out_vals = (double*)realloc(out_vals, sizeof(double) * (out_capacity * 2));
        out_capacity *= 2;
      }
      out_vals[jout] = B_vals[jB];
      if (out2_crd_size <= jout) {
        out2_crd = (int32_t*)realloc(out2_crd, sizeof(int32_t) * (out2_crd_size * 2));
        out2_crd_size *= 2;
      }
      out2_crd[jout] = j;
      jout++;
      jB++;
    }

    out2_pos[i + 1] = jout - pout2_begin;
  }

  int32_t csout2 = 0;
  for (int32_t pout20 = 1; pout20 < (out1_dimension + 1); pout20++) {
    csout2 += out2_pos[pout20];
    out2_pos[pout20] = csout2;
  }

  out->indices[1][0] = (uint8_t*)(out2_pos);
  out->indices[1][1] = (uint8_t*)(out2_crd);
  out->vals = (uint8_t*)out_vals;
  return 0;
}

