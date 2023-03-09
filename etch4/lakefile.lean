import Lake
open Lake DSL

package etch
lean_lib Etch

@[default_target]
lean_exe sep {
  root := `Main
}

--require aesop from git
--  "https://github.com/JLimperg/aesop"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4/"@"ac9bdd4dbac2bf11cb15f3081a0d38f1ec4b7012"
  -- "01a2153b1daa21e2a309e795c3d259bba5e77a27"
--require mathlib from git
--  "https://github.com/leanprover-community/mathlib4/"

lean_exe bench where
  root := `Etch.Benchmark
