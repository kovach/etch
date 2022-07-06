  //auto t2 = std::chrono::high_resolution_clock::now();
  // cout << "out: " << out << endl;
  // cout << "out1_i: " << out1_i << ",  out2_i: " << out2_i << endl;
  // cout << "A1_i: " << A1_i << ",  A2_i: " << A2_i << endl;
  // cout << "B1_i: " << B1_i << ",  B2_i: " << B2_i << endl;
  //std::cout << "took: " << std::chrono::duration_cast<std::chrono::milliseconds>(t2-t1).count() << std::endl;

  //taco_ijk_sum();
  //taco_ikjk();

  if (out2_i < 30 && A2_i < 30) {
    cout << "a1_crd: ";
    for (int i = 0; i < A1_i+1; i++)
      cout << A1_crd[i] << ", ";
    cout << endl;
    cout << "a2_pos: ";
    for (int i = 0; i < A1_i+1; i++)
      cout << A2_pos[i] << ", ";
    cout << endl;
    cout << "a2: ";
    for (int i = 0; i < A2_i+1; i++)
      cout << A2_crd[i] << ", ";
    cout << endl;
    cout << "A values: ";
    for (int i = 0; i < A2_i+1; i++)
      cout << A_vals[i] << ", ";
    cout << endl;
    cout << "out values: ";
    for (int i = 0; i < out2_i+1; i++)
      cout << out_vals[i] << ", ";
    cout << endl;
    return 0;
  }
}
