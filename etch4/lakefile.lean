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
  "https://github.com/leanprover-community/mathlib4/"@"f493ef4c7bbdfc42f14962390c505c097a1650f9"
