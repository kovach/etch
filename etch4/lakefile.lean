import Lake
open Lake DSL

package etch
lean_lib Etch

@[default_target]
lean_exe bench {
  root := `Etch.Benchmark
}

@[default_target]
lean_lib Etch.Verification.Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4/"@"d04897a61efc29f2393f448154f212472c91b47d"
