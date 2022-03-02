printf("a %d\n", a);
printf("b %d\n", b);
  for(int i = 0; i < BUFFER_SIZE; i++) {
    printf("%d:%f\n", i, (float)acc[i]);
  }
}
