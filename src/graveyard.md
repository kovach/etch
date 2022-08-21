The commit which adds this file removes several old prototype compilers.
They explored some design decisions that did not pan out, but may still be of interest:

# main3.hs
This encoding of Gen used "double negation" for all fields (`current, value, next`),
an idea originally inspired by https://arxiv.org/pdf/1612.06668.pdf.
This implementation was the first to create working code,
but suffered from pretty terrible blow-up in size:
at one point I generated a matrix multiply with 150k lines of code.
Removing redundant conditional checks and dead branches made the output workable,
but it still struggled with quite small input problems.
The definitions of combinators are also quite hard to read and probably not optimal.

Code generation is based on flatten, which uncurries an iterator.
We combine a stream (of r-values) with a locatable stream (of l-values) to produce a stream of code values, which we then flatten and iterate with one top-level loop.

# main4.hs
The primary change from main3 is that `current, value` are direct values
and only next is `(Maybe T -> T) -> T`.
Code output size is significantly reduced. `addGen` is never defined in this version.
This serves as the model for the initial translation into lean,`compile.lean`

# compile.lean
Faithful translation of main4, with just a few Lean tricks.
We notice that performance of the reader/writer/state monad stack is very bad,
but fixed if we remove `Writer`.

# notes on current prototypes
`compile_fast.lean` (not removed by this commit):
Compilation strategy significantly changes: instead of flattening a nested iterator into one loop,
we define a code-generation class which generates one loop per level.
The resulting code has a far more readable loop structure.
We no longer need to "figure out" what loop we're currently in each time we resume the top level loop.
We also implement the sparse data representation needed for csr/dcsr formats
and perform comparisons to TACO: performance is basically the same.

`compile_fast2.lean` (not removed by this commit):
Work in progress port of `compile_fast` to new `Prog` type (which can be evaluated).
