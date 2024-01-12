import Lake
open Lake DSL

package etch

lean_lib Etch where defaultFacets := #[LeanLib.sharedFacet]

@[default_target]
lean_exe bench {
  root := `Etch.Benchmark
}

@[default_target]
lean_exe myrun {
  root := `Etch.ComputableStreams2
  moreLeancArgs := #["-fno-omit-frame-pointer", "-g"]
}

@[default_target]
lean_lib Etch.Verification.Main

@[default_target]
lean_lib Etch.Compile.Ext
  where defaultFacets := #[LeanLib.sharedFacet]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4/"@"a2ca43e594f2f3d1ccbb2cf178fd5800abc61321"
