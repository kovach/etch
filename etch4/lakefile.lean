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
  --"ca97e7ba874708c46ddfc25165f9bc1a75c5b8cc"
--require mathlib from git
--  "https://github.com/leanprover-community/mathlib4/"
