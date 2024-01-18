import Mathlib.Data.Fintype.Card
import Etch.Verification.Semantics.SkipStream

/-!
# Dense Vectors as Indexed Streams (sanity check)

In this file, we show that `denseVec` (modelling dense vectors as a stream)
satisfies the stream conditions (it is strictly lawful); therefore our conditions are not vacuous.
A similar thing can be done for sparse vectors.

This is mostly a lot of tedious casework. TODO: can we automate this to an SMT solver?

## Definitions:
We define `Stream.denseVec vals`, which takes a vector `vals` and constructs
an always-ready stream that outputs the elements of `vals`. The state of `denseVec`
is considered to be `fin (n + 1)`, the natural numbers `0 ≤ q ≤ n`, where `q : fin (n + 1)` is the terminated state

## Main results:
  - `Stream.denseVec_eval`: Evaluating from a state `q : fin (n + 1)` results in
      emitting `vals[q:]` at the appropriate indices.
        - Corollary (`Stream.denseVec_eval_start`): Starting from `q = 0` produces the whole vector.
  - `is_strict_lawful (Stream.denseVec vals)`: The stream associated with a dense vector is strictly lawful
-/

set_option linter.uppercaseLean3 false

namespace Etch.Verification

variable {α : Type _}

def Stream.denseVec {n : ℕ} (vals : Fin n → α) : Stream (Fin n) α where
  σ := Fin (n + 1)
  valid i := ↑i < n
  ready i := ↑i < n
  skip i _hi j := max i (cond j.2 j.1.succ (Fin.castLE n.le_succ j.1))
  index i hi := i.castLT hi
  value i hi := vals (i.castLT hi)
#align Stream.denseVec Etch.Verification.Stream.denseVec

attribute [reducible] Stream.denseVec in
section

instance {n} (vals : Fin n → α) : IsBounded (Stream.denseVec vals) :=
  ⟨⟨⟨(· > ·), Finite.to_wellFoundedGT.wf⟩,
    fun i hi j => by
      unfold Stream.toOrder
      rw [Prod.Lex.lt_iff'']
      rcases i with ⟨i, ip⟩
      rcases j with ⟨⟨j, jp⟩, b | b⟩
      · suffices j ≤ i → (j ≤ i ∧ (j = i → i < n)) ∧ j ≤ i by
          simpa [or_iff_not_imp_left, decide_eq_true_iff _] using this
        intro h
        have : j = i → i < n := fun a => a ▸ jp
        simpa [h] using this
      · simpa [lt_iff_not_le (x := true), imp_false, ← lt_iff_le_and_ne,
          Nat.lt_succ_iff, Nat.succ_le_iff] using le_or_lt i j⟩⟩

variable [AddZeroClass α]

theorem Fin.castLT_le_iff {m n : ℕ} (a b : Fin n) (h₁ : ↑a < m) (h₂ : ↑b < m) :
    a.castLT h₁ ≤ b.castLT h₂ ↔ a ≤ b :=
  by cases a; cases b; simp
#align fin.cast_lt_le_iff Etch.Verification.Fin.castLT_le_iff

theorem Stream.denseVec.eq_n_of_invalid {n : ℕ} {vals : Fin n → α} {q : Fin (n + 1)}
    (hq : ¬(Stream.denseVec vals).valid q) : ↑q = n :=
  eq_of_le_of_not_lt (Nat.lt_succ_iff.mp q.prop) hq
#align Stream.denseVec.eq_n_of_invalid Etch.Verification.Stream.denseVec.eq_n_of_invalid

theorem Stream.denseVec_eval {n : ℕ} (vals : Fin n → α) (q : Fin (n + 1)) :
    (Stream.denseVec vals).eval q = fun j => if Fin.castSucc j < q then 0 else vals j := by
  apply (Stream.denseVec vals).wf.induction q
  clear q; intro q ih
  by_cases hq : (Stream.denseVec vals).valid q; swap
  · replace hq : ↑q = n := Stream.denseVec.eq_n_of_invalid hq
    rw [Stream.eval_invalid]
    swap
    · exact hq.not_lt
    · ext j
      have : Fin.castSucc j < q := by
        rw [Fin.lt_iff_val_lt_val]
        rw [hq]
        simp
      simp only [this, Finsupp.coe_zero, Pi.zero_apply, if_true]
  · rw [Stream.eval_valid, Stream.eval₀, dif_pos] <;> try exact hq
    ext j
    rw [Finsupp.add_apply, ih _ ((Stream.denseVec vals).next_wf q hq)]
    dsimp only
    rcases lt_trichotomy (Fin.castSucc j) q with (h | h | h)
    · rw [if_pos, add_zero]; swap
      · simp [Stream.next_val hq]
        left; assumption
      · rw [if_pos]; swap
        · assumption
        · rw [Finsupp.single_apply_eq_zero]
          intro h'
          exfalso
          refine h.not_le ?_
          simp [h']
    · have : Fin.castLT q hq = j := by simp [← h]
      rw [if_pos, add_zero]; swap
      · simp [Stream.next_val hq, show ↑q < n from hq]
        right
        rw [this]
        exact Fin.castSucc_lt_succ _
      · rw [if_neg]
        · simp [this]
        · exact h.not_lt
    · rw [if_neg]; swap
      · simp [Stream.next_val hq, show ↑q < n from hq, not_or]
        revert h
        cases j; cases q
        simp [Nat.succ_le_iff]
        intro h
        exact ⟨h.le, h⟩
      · rw [if_neg]; swap
        · exact h.le.not_lt
        · rw [Finsupp.single_apply_eq_zero.mpr, zero_add]
          rintro rfl
          exfalso
          simp at h
#align Stream.denseVec_eval Etch.Verification.Stream.denseVec_eval

@[simp]
theorem Stream.denseVec_eval_start {n : ℕ} (vals : Fin n → α) :
    (Stream.denseVec vals).eval 0 = vals := by
  rw [Stream.denseVec_eval]
  ext j
  exact if_neg (Fin.not_lt_zero _)
#align Stream.denseVec_eval_start Etch.Verification.Stream.denseVec_eval_start

variable (v : Fin n → α) in
#synth DecidablePred (Stream.denseVec v).ready

instance {n} (vals : Fin n → α) : IsLawful (Stream.denseVec vals) where
  mono :=
    (Stream.isMonotonic_iff (s := Stream.denseVec vals)).mpr fun q hq i hq' => by
      dsimp
      rw [Fin.castLT_le_iff]
      exact le_max_left _ _
  skip_spec q hq i j hj := by
    simp only [Stream.denseVec_eval]
    by_cases h₁ : Fin.castSucc j < q; · simp [h₁]
    rwa [if_neg, if_neg]
    rw [lt_max_iff, not_or]
    refine ⟨h₁, ?_⟩
    rw [not_lt]
    rcases i with ⟨i, b | b⟩ <;> simp only [cond]
    · rw [Fin.castSucc, Fin.castAdd]
      simpa using hj
    · rw [← Fin.castSucc_lt_iff_succ_le]
      simpa [Prod.Lex.le_iff'] using hj

@[simp]
theorem Stream.denseVec_eval_start_apply {n} (vals : Fin n → α) (i : Fin n) :
    (Stream.denseVec vals).eval 0 i = vals i := by simp

theorem Stream.denseVec_index'_mono {n} (vals : Fin n → α) :
    StrictMono (Stream.denseVec vals).index' := fun q₁ q₂ => by
  unfold Stream.index'; split_ifs with h₁ h₂ h₂
  · cases q₁; cases q₂
    simp
  · simp only [WithTop.coe_lt_top]
    exact fun _ => trivial
  · simp only [not_top_lt, not_lt, Fin.lt_iff_val_lt_val, Stream.denseVec.eq_n_of_invalid h₁,
      imp_false]
    exact Nat.lt_succ_iff.mp q₂.prop
  · simp [Stream.denseVec.eq_n_of_invalid h₁, Stream.denseVec.eq_n_of_invalid h₂,
     Fin.lt_iff_val_lt_val]
#align Stream.denseVec_index'_mono Etch.Verification.Stream.denseVec_index'_mono

instance {n} (vals : Fin n → α) : IsStrictLawful (Stream.denseVec vals) :=
  ⟨⟨Stream.mono _, fun q hq i hi hr =>
      ne_of_lt
        (by
          apply Stream.denseVec_index'_mono
          rcases i with ⟨i, b⟩
          suffices q < cond b i.succ (Fin.castSucc i) by
            dsimp only
            rw [max_eq_right]
            · exact this
            · exact this.le
          simp only [Stream.toOrder, show ↑q < n from hq, decide_True'] at hi
          cases i
          cases q
          cases b <;> simpa [Nat.lt_succ_iff] using hi)⟩⟩

end

end Etch.Verification
