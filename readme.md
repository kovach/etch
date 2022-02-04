# intro

This is a work-in-progress formalization of _indexed streams_ (see `iter` in `src/base.lean`),
which model automata that compute sparse vectors.

The latest theorem is `add_iter_sound`.

# build

First install [lean3](https://leanprover-community.github.io/get_started.html).
In the root directory, run
```
leanproject get-mathlib-cache
leanproject build
```
