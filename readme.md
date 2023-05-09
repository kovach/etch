# Etch

This repository implements indexed streams, a way to represent fused
"contraction programs" like those found in sparse tensor algebra and relational
algebra.

Correctness proofs are written in [Lean 3][lean3], while the compiler is
written in the [Lean 4][lean4] language. We hope to port the proofs to Lean 4
soon.

[lean3]: https://github.com/leanprover-community/lean
[lean4]: https://github.com/leanprover/lean4

## Directory structure

### Correctness proofs

```
.
└── src
    ├── verification
    │   ├── code_generation           # WIP code generation proofs
    │   │   ├── vars.lean
    │   │   └── verify.lean
    │   ├── semantics                 # correctness proofs
    │   │   ├── README.md
    │   │   ├── ...
    │   ├── stream_split.lean         # (should be moved to semantics/)
    │   └── test.lean
    ├── graveyard.md                  # ideas that didn't work out
    ├── compile.lean                  # old compiler (deprecated in favor of etch4/)
    ├── compile_fast.lean
    ├── compile2.lean
    ├── front_end.lean
    ├── tactic.lean
    ├── declare.lean                  # old formalization (deprecated in favor of src/verification/)
    └── old_formalization
        └── ...
```

### Compiler and benchmarks

```
etch4
├── Etch                          # the compiler
│   ├── Basic.lean                # compiler core
│   ├── C.lean
│   ├── Compile.lean
│   ├── LVal.lean
│   ├── Op.lean
│   ├── ShapeInference.lean
│   ├── Stream.lean
│   ├── Add.lean                  # basic streams
│   ├── Mul.lean
│   ├── Benchmark.lean            # benchmark queries
│   ├── Benchmark
│   │   └── ...
│   ├── KRelation.lean            # work in progress
│   ├── Omni.lean
│   └── InductiveStream…
├── Makefile                      # workflows
├── bench                         # benchmark auxiliary files (SQL files, data generators, etc.)
│   └── ...
├── bench-….cpp                   # benchmark drivers
├── common.h
├── operators.h
├── graphs                        # run benchmarks; plot graphs
│   └── ...
├── taco                          # TACO-compiled kernels as baseline
│   └── ...
└── taco_kernels.c
```

## Build proofs

First install [Lean 3](https://leanprover-community.github.io/get_started.html).
In the root directory, run
```
leanproject get-mathlib-cache
leanproject build
```

## Build compiler

First install [Lean 4](https://leanprover.github.io/lean4/doc/quickstart.html).
In the `etch4` directory, run
```
lake update
lake exe cache get
lake build
```
Then, load Etch/Benchmark.lean in your editor.

### Compile benchmarks

While loading the Etch/Benchmark.lean in your editor, Lean will automatically
compile all the benchmarks and write them to `etch4/gen_….c`.

Alternatively, you can compile by running `make gen_tpch_q5.c FORCE_REGEN=1`.

### Running benchmarks

Only Linux is supported right now.

Dependencies you need to have before running any benchmarks:
* `make` ([GNU Make](https://www.gnu.org/software/make/))
* `clang` ([LLVM Clang](https://clang.llvm.org/))
* `bc` ([GNU bc](https://www.gnu.org/software/bc/))

Other dependencies (e.g., baselines) are automatically downloaded by the
Makefile.

#### Run individual benchmarks

You can run an individual benchmark by calling `make`. Here are some examples:
```
make run-tpch-x1-q5-duckdb
make run-tpch-x1-q5-duckdbforeign
make run-tpch-x1-q5-etch
make run-tpch-x1-q5-sqlite

make run-wcoj-x1000-etch
```

If any test data need to be (re-)generated, the above commands will
automatically do so.

For a full list of supported targets, run `make list-benchmarks`.

#### Run all benchmarks

Run `graphs/run.sh`.
This will run all the benchmarks shown in our PLDI 2023 paper, and save the
results in bench-output/.

Note: this will take a **long** time (≥1.5 hours).

#### Generate graphs

Make sure all the benchmarks have been run with `graphs/run.sh`.

Make sure the benchmark results are stored in bench-output/.

Make sure you have [Poetry](https://python-poetry.org/) (a Python package
manager) installed.

Then run:
```
cd graphs
poetry install
poetry shell
cd ..
python graphs/graph.py
```

Graphs will be generated in PDF form in the root directory.

#### Running benchmarks in Docker

We also provide a Dockerfile to simplify the process of setting up an
environment. This is primarily useful for artifact evaluation. See
`graphs/Dockerfile` for details.

If you will be developing Etch locally, we recommend going through the previous
steps instead.

## Publications

This repo implements indexed streams as defined in this paper:

> Scott Kovach, Praneeth Kolichala, Tiancheng Gu, and Fredrik Kjolstad. 2023.
> Indexed Streams: A Formal Intermediate Representation for Fused Contraction
> Programs. To appear in <em><cite>Proc. ACM Program. Lang.</cite></em> 7,
> PLDI, Article 154 (June 2023), 25 pages. https://doi.org/10.1145/3591268

A preprint is available at https://cutfree.net/PLDI_2023_indexed_streams.pdf.

There's also an earlier preprint:

> Scott Kovach and Fredrik Kjolstad. 2022. Correct Compilation of Semiring
> Contractions. arXiv:[2207.13291](https://arxiv.org/abs/2207.13291) [cs.PL]
