import Etch.Verification.CodeGen.Translate
import Etch.Verification.Semantics.Sparse

namespace Etch.Verification
section
open Expr

def SSparse (inds : ℕ) (vals : ℕ) (n : ℕ) : S ℕ ℤ where
  σ := Unit
  σ_enc := inferInstance
  Γ := fun _ => ℕ
  -- TODO: make a DSL to make it easier to write this code?
  valid := lt (τ := ℕ) (var (by exact ())) (glb CType.nn n)
  ready := op (.boolLit true) finZeroElim
  skip₀ := sorry
  skip₁ := sorry
  index := op .arrAccess ![glb (.lst .nn) inds, var (by exact ())]
  value := op .arrAccess ![glb (.lst .rr) vals, var (by exact ())]
  init := .store (.var (by exact ())) (0 : Expr _ ℕ)

def SSparse.validInputs (inds : ℕ) (vals : ℕ) (n : ℕ) : Set GlobalVars :=
{ g | List.Sorted (α := ℕ) (· ≤ ·) (g (.lst .nn) inds)
      ∧ (g (.lst .nn) inds).length = g .nn n
      ∧ (g (.lst .rr) vals).length = g .nn n }

theorem SSparse.tr (inds : ℕ) (vals : ℕ) (n : ℕ) :
    tr (SSparse.validInputs inds vals n) 
      (fun g hg => Stream.sparseVec (ι := ℕ) ⟨g (.lst .nn) inds, hg.2.1⟩ ⟨g (.lst .rr) vals, hg.2.2⟩)
      (SSparse inds vals n) := by
  intros g hg
  refine ⟨fun (q : ℕ) _ => q, ?_⟩
  dsimp only
  intro q
  constructor
  · simp [SSparse, Expr.lt_eval]; rfl
  · sorry
  · sorry
  · sorry
  · dsimp; sorry
  · dsimp; sorry 

end



end Etch.Verification


