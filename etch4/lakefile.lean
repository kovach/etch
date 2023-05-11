import Lake
open Lake DSL

package etch
lean_lib Etch

@[default_target]
lean_exe bench {
  root := `Etch.Benchmark
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4/"@"5ed65e18440bf46dc8dda58b5463377f938d717c"
