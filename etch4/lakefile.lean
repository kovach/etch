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
  "https://github.com/leanprover-community/mathlib4/"@"84ef023de00c7266ab589e59eba2acc1bf8f7b99"
  --"ca97e7ba874708c46ddfc25165f9bc1a75c5b8cc"
--require mathlib from git
--  "https://github.com/leanprover-community/mathlib4/"
