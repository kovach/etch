import Etch.Verification.CodeGen.Translate

namespace Etch.Verification
section
open Expr

def SSparse (inds : ℕ) (vals : ℕ) : S ℕ ℤ where
  σ := Unit
  σ_enc := inferInstance
  Γ := fun _ => ℕ
  -- TODO: make a DSL to make it easier to write this code?
  valid := lt (τ := ℕ) (var (by exact ())) (glb CType.nn inds)
  ready := op (.boolLit true) finZeroElim
  skip₀ := sorry
  skip₁ := sorry
  index := op .arrAccess ![glb (.lst .nn) inds, var (by exact ())]
  value := op .arrAccess ![glb (.lst .rr) vals, var (by exact ())]
  init := .store (τ := ℕ) (.var (by exact ())) (op (.natLit 0) finZeroElim)

end
end Etch.Verification


