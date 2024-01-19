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
  root := `Etch.StreamFusion.Stream
  moreLeancArgs := #["-fno-omit-frame-pointer", "-g"]
}

@[default_target]
lean_lib Etch.Verification.Semantics.Example

require mathlib from git
  "https://github.com/leanprover-community/mathlib4/"@"702f3fe16c773ae1e34fbf179342d0877f8cb4f1"
