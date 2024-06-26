import Lake
open Lake DSL

package etch

lean_lib Etch where defaultFacets := #[LeanLib.sharedFacet]

@[default_target]
lean_exe bench {
  root := `Etch.Benchmark
}

@[default_target]
lean_exe proofs {
  root := `Etch.StreamFusion.Proofs.Proofs
}

@[default_target]
lean_exe fusion {
  root := `Etch.StreamFusion.Main
  moreLeancArgs := #["-fno-omit-frame-pointer", "-g"]
}

lean_exe fusion_mat {
  root := `Etch.StreamFusion.MainMatrix
  moreLeancArgs := #["-fno-omit-frame-pointer", "-g"]
}

@[default_target]
lean_exe eg {
  root := `Etch.StreamFusion.Examples.Benchmarks
  moreLeancArgs := #["-fno-omit-frame-pointer", "-g"]
}

lean_exe tutorial {
  root := `Etch.StreamFusion.Tutorial
  moreLeancArgs := #["-fno-omit-frame-pointer", "-g"]
}

lean_exe reuse {
  root := `Etch.StreamFusion.ReuseTest
  moreLeancArgs := #["-fno-omit-frame-pointer", "-g"]
}

lean_exe seq {
  root := `Etch.StreamFusion.Sequence
  moreLeancArgs := #["-fno-omit-frame-pointer", "-g"]
}

@[default_target]
lean_lib Etch.Verification.Semantics.Example

require mathlib from git
  "https://github.com/leanprover-community/mathlib4/"@"3897434e80c1e66658416557947b9b9604e336a7"
