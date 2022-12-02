# intro

This repository implements [indexed streams](https://arxiv.org/abs/2207.13291).

See [here](src/compile_fast.lean) for the compiler and [here](src/front_end.lean) for several example array kernels.

# build proofs

First install [lean3](https://leanprover-community.github.io/get_started.html).
In the root directory, run
```
leanproject get-mathlib-cache
leanproject build
```

# build compiler

First install [lean4](https://leanprover.github.io/lean4/doc/quickstart.html).
In the `etch4` directory, run
```
lake build
```
then load Etch/Benchmark.lean in your editor.
