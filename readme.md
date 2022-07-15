# intro

This is a work-in-progress formalization of _indexed streams,_
which model automata that compute sparse vectors.

See [here](src/compile_fast.lean) for the compiler and [here](src/front_end.lean) for several example array kernels.

# build

First install [lean3](https://leanprover-community.github.io/get_started.html).
In the root directory, run
```
leanproject get-mathlib-cache
leanproject build
```
