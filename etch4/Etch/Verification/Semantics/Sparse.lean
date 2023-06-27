import Mathlib.Order.WellFoundedSet
import Etch.Verification.Semantics.SkipStream
import Etch.Verification.Misc

/-! 
# Sparse Vectors

-/

namespace Etch.Verification

variable {ι α : Type _} [LinearOrder ι] {n : ℕ}

open Streams

theorem IsBounded.mkWfSubset {s : Stream ι α}
  (r : s.σ → s.σ → Prop) (wf : Set.WellFoundedOn {q | s.valid q} r) 
  (hr : ∀ q hq i, r (s.skip q hq i) q ∨ (i <ₗ s.toOrder q hq) ∧ s.skip q hq i = q) :
    IsBounded s := by
  refine ⟨⟨_, wf.adjoin_compl_as_bot⟩, fun q hq i => ?_⟩
  refine (hr q hq i).imp_left ?_
  simpa only [Set.mem_setOf_eq, hq, true_and] using Function.const _

def Stream.sparseVec (inds : Vector ι n) (vals : Vector α n) :
    Stream ι α where
  σ := ℕ
  valid := fun i => i < n
  ready := fun i => i < n
  skip := fun i _ jb => ((Fin.find fun k : Fin n => i ≤ k ∧ jb.1 ≤ inds.get k ∧ (jb.2 → jb.1 < inds.get k)).map Fin.val).getD n
  index := fun i hi => inds.get ⟨i, hi⟩
  value := fun i hi => vals.get ⟨i, hi⟩

attribute [reducible] Stream.sparseVec in
theorem Stream.sparseVec_isBounded (inds : Vector ι n) (vals : Vector α n) :
    IsBounded (Stream.sparseVec inds vals) :=
  IsBounded.mkWfSubset (· > ·) (Set.Finite.wellFoundedOn sorry) (by
    rintro q hq ⟨j, b⟩; simp only [Stream.toOrder] at hq ⊢; simp
    sorry
  )



end Etch.Verification
