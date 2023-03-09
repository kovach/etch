# pldi23 artifact evaluation

Our artifact contains two main components:
  - formal proofs of combinator correctness described in section 7.3
    - located in `src/`
    - `src/verification/test.lean` contains example code from the figures
  - the compiler described in section 8 and evaluation scripts used for section 9
    - located in `etch4/`

The included dockerfile includes prebuilt proof binaries and the WCOJ scaling
figure from section 9. After loading the included docker image .tar.gz file,
you can view the output of the other benchmarks using
  docker run -it 3d0364f0c2fa ./out
This prints a human-readable summary of the TACO and sqlite comparisons.

To browse the proofs interactively, it is recommended to perform a standard local installation of Lean and VSCode.
  - see: https://leanprover-community.github.io/get_started.html

For the TACO benchmarks, some minor changes were made to the compiler since
submission that improve relative performance.

Notes on the worst-case optimal join figure: Our scripts generate a plot that
is improved from the one in the paper. It is generated from a query which ETCH
and other optimal algorithms can solve in linear time, whereas SQLite and other
pair-wise algorithms require quadratic time. This is shown via the slopes in
the log-log plot (the vertical offset is included for ease of viewing only;
ETCH solves the query several orders of magnitude faster than SQLite).
Relative to the paper, no changes were made to the query code, only a more
challenging input dataset was selected.
