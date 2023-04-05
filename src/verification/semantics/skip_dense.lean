import verification.semantics.skip_stream

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



variables {α : Type*}


def Stream.denseVec {n : ℕ} (vals : vector α n) : Stream (fin n) α :=
{ σ := fin (n + 1),
  valid := λ i, ↑i < n,
  ready := λ i, ↑i < n,
  skip := λ i hi j, max i (cond j.2 j.1.succ (fin.cast_le n.le_succ j.1)),
  index := λ i hi, i.cast_lt hi,
  value := λ i hi, vals.nth (i.cast_lt hi), }

section
variables [add_zero_class α]
local attribute [reducible] Stream.denseVec

instance {n} (vals : vector α n) : is_bounded (Stream.denseVec vals) :=
⟨⟨(>), finite.preorder.well_founded_gt, λ i hi j, begin
  simp [Stream.to_order, hi],
  rcases j with ⟨j, (b|b)⟩,
  { rw prod.lex.lt_iff'', cases j, cases i, simp, rw [or_iff_not_imp_left, not_lt], tauto, },
  { rw prod.lex.lt_iff'', cases i, cases j, simp [@lt_iff_not_le _ _ tt, imp_false, ← lt_iff_le_and_ne, nat.lt_succ_iff, nat.succ_le_iff], exact le_or_lt _ _, },
end⟩⟩

lemma fin.cast_lt_le_iff {m n : ℕ} (a b : fin n) (h₁ : ↑a < m) (h₂ : ↑b < m) :
  a.cast_lt h₁ ≤ b.cast_lt h₂ ↔ a ≤ b :=
by { cases a, cases b, simp, }

lemma Stream.denseVec.eq_n_of_invalid {n : ℕ} {vals : vector α n} {q : fin (n + 1)}
  (hq : ¬(Stream.denseVec vals).valid q) : ↑q = n := eq_of_le_of_not_lt (nat.lt_succ_iff.mp q.prop) hq

lemma Stream.denseVec_eval {n : ℕ} (vals : vector α n) (q : fin (n + 1)) :
  ⇑((Stream.denseVec vals).eval q) = (λ j, if (fin.cast_succ j) < q then 0 else vals.nth j) :=
begin
  refine @well_founded.induction _ _ (Stream.denseVec vals).wf _ q _,
  clear q, intros q ih,
  by_cases hq : (Stream.denseVec vals).valid q, swap,
  { replace hq : ↑q = n := Stream.denseVec.eq_n_of_invalid hq,
    rw [Stream.eval_invalid], swap, { exact hq.not_lt, },
    ext j,
    have : (fin.cast_succ j) < q, { rw fin.lt_iff_coe_lt_coe, rw hq, simp, },
    simp only [this, finsupp.coe_zero, pi.zero_apply, if_true], },
  { rw [Stream.eval_valid, Stream.eval₀, dif_pos]; try { exact hq },
    ext j,
    rw [finsupp.add_apply, ih _ ((Stream.denseVec vals).next_wf q hq)], dsimp only,
    rcases lt_trichotomy (fin.cast_succ j) q with (h|h|h),
    { rw [if_pos, add_zero], swap, { simp [Stream.next_val hq], left, assumption, },
      rw [if_pos], swap, { assumption, },
      rw finsupp.single_apply_eq_zero, intro h', exfalso, refine h.not_le _,
      simp [h'], },
    { have : fin.cast_lt q hq = j, { simp [← h], },
      rw [if_pos, add_zero], swap, { simp [Stream.next_val hq, (show ↑q < n, from hq)], right, rw this, exact fin.cast_succ_lt_succ _, },
      rw [if_neg], swap, { exact h.not_lt, },
      simp [this], },
    { rw [if_neg], swap, { simp [Stream.next_val hq, (show ↑q < n, from hq), not_or_distrib], revert h, cases j, cases q, simp [nat.succ_le_iff], intro h, exact ⟨h.le, h⟩, },
      rw [if_neg], swap, { exact h.le.not_lt, },
      rw [finsupp.single_apply_eq_zero.mpr, zero_add],
      rintro rfl, exfalso, simpa using h, } },
end

lemma Stream.denseVec_eval_start {n : ℕ} (vals : vector α n) :
  ⇑((Stream.denseVec vals).eval 0) = vals.nth :=
by { rw Stream.denseVec_eval, ext j, simp, }

instance {n} (vals : vector α n) : is_lawful (Stream.denseVec vals) :=
{ mono := Stream.is_monotonic_iff.mpr $ λ q hq i hq', by { dsimp, rw fin.cast_lt_le_iff, exact le_max_left _ _, },
  skip_spec := λ q hq i j hj, begin
    simp only [Stream.denseVec_eval],
    by_cases h₁ : fin.cast_succ j < q, { simp [h₁], },
    rw [if_neg, if_neg], { assumption, },
    rw [lt_max_iff, not_or_distrib],
    refine ⟨h₁, _⟩, rw [not_lt],
    rcases i with ⟨i, (b|b)⟩; simp only [cond],
    { rw [fin.cast_succ, fin.cast_add, order_embedding.le_iff_le],
      simpa using hj, },
    { rw ← fin.cast_succ_lt_iff_succ_le,
      simpa [prod.lex.le_iff'] using hj, },
  end }

lemma Stream.denseVec_index'_mono {n} (vals : vector α n) : strict_mono (Stream.denseVec vals).index' :=
λ q₁ q₂, begin
  simp only [Stream.index'], split_ifs with h₁ h₂ h₂,
  { cases q₁, cases q₂, simp, }, { simp only [with_top.coe_lt_top], exact λ _, trivial, },
  { simp only [not_top_lt, not_lt, fin.lt_iff_coe_lt_coe, Stream.denseVec.eq_n_of_invalid h₁, imp_false], exact nat.lt_succ_iff.mp q₂.prop, },
  { simp [Stream.denseVec.eq_n_of_invalid h₁, Stream.denseVec.eq_n_of_invalid h₂, fin.lt_iff_coe_lt_coe], },
end

instance {n} (vals : vector α n) : is_strict_lawful (Stream.denseVec vals) :=
⟨⟨Stream.mono _, λ q hq i hi hr, ne_of_lt begin
  apply Stream.denseVec_index'_mono,
  rcases i with ⟨i, b⟩, dsimp only,
  suffices : q < cond b i.succ (fin.cast_succ i),
  { rw max_eq_right, { exact this, }, exact this.le, },
  simp only [Stream.to_order, (show ↑q < n, from hq), to_bool_true_eq_tt] at hi,
  cases i, cases q, cases b; simpa [nat.lt_succ_iff] using hi,
end⟩⟩

end

