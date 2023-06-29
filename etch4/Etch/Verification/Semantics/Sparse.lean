import Mathlib.Order.WellFoundedSet
import Mathlib.Order.Basic
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
  skip := fun i hi jb => 
    .find (p := fun k => i ≤ k ∧ ((hk : k < n) → jb < (inds.get ⟨k, hk⟩, true))) 
      ⟨n, hi.le, fun hk => absurd hk (lt_irrefl n)⟩
    --((Fin.find fun k : Fin n => i ≤ k ∧ jb.1 ≤ inds.get k ∧ (jb.2 → jb.1 < inds.get k)).map Fin.val).getD n
  index := fun i hi => inds.get ⟨i, hi⟩
  value := fun i hi => vals.get ⟨i, hi⟩

lemma Stream.sparseVec_toOrder (inds : Vector ι n) (vals : Vector α n)
  (q : (Stream.sparseVec inds vals).σ) (hq : Stream.valid _ q) :
    (Stream.sparseVec inds vals).toOrder q hq = (inds.get ⟨q, hq⟩, true) := by
  apply Prod.ext
  · rfl
  · simp [sparseVec, show (@LT.lt ℕ _ q n) from hq]

attribute [reducible] Stream.sparseVec in
theorem Stream.sparseVec_isBounded (inds : Vector ι n) (vals : Vector α n) :
    IsBounded (Stream.sparseVec inds vals) :=
  IsBounded.mkWfSubset (@GT.gt ℕ _) (Set.Finite.wellFoundedOn (α := ℕ) sorry) (by
    rintro q hq jb; simp only [gt_iff_lt]
    by_cases H : jb <ₗ toOrder (sparseVec inds vals) q hq
    · right; refine ⟨H, ?_⟩
      rw [Stream.sparseVec_toOrder] at H
      simp only [Nat.find_eq_iff, le_refl, true_and, not_and, not_forall, not_lt]
      constructor
      · intro hk
        convert H
      · intros n h₁ h₂
        exact absurd h₂ h₁.not_le
    · left; rw [Stream.sparseVec_toOrder] at H
      simp only [Nat.lt_find_iff, not_and, not_forall, not_lt]
      intros m h₁ h₂
      obtain rfl : m = q := le_antisymm h₁ h₂
      exact ⟨hq, le_of_not_lt H⟩





  )

end Etch.Verification
