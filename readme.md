# pldi23 artifact evaluation

Our artifact contains two main components:
  - formal proofs of combinator correctness described in section 7.3
    - located in `src/`
    - `src/verification/test.lean` contains code from the figures
  - the compiler described in section 8 and evaluation scripts used for section 9
    - located in `etch4/`

The included dockerfile includes prebuilt proof binaries and the WCOJ scaling figure from section 9.
After loading the included docker image .tar.gz file, you can view the output of the other benchmarks using
  docker run -it 3d0364f0c2fa ./out
This prints a human-readable summary of the TACO and sqlite comparisons.

To browse the proofs interactively, it is recommended to perform a standard local installation of Lean and VSCode.
  - see: https://leanprover-community.github.io/get_started.html

