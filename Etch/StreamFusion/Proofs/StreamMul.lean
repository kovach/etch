import Etch.StreamFusion.Proofs.StreamProof
import Etch.StreamFusion.Multiply

namespace Etch.Verification.Stream

open Streams

universe u
variable {ι : Type} [LinearOrder ι] {α : Type u}

section IndexLemmas

variable [Mul α]

theorem mul.ready.order_eq {a : Stream ι α} {b : Stream ι α} {q}
    (h : mul.ready a b q) : a.toOrder (mul.valid.fst q) = b.toOrder (mul.valid.snd q) := by
  dsimp only [Stream.toOrder]
  aesop

theorem order_eq_of_mul_ready {a : Stream ι α} {b : Stream ι α} {q}
    (h : mul.ready a b q) : a.toOrder (mul.valid.fst q) = (a.mul b).toOrder q ∧
      b.toOrder (mul.valid.snd q) = (a.mul b).toOrder q := by
  dsimp only [Stream.toOrder]
  aesop

theorem Stream.mul_index' (a : Stream ι α) (b : Stream ι α) (q) :
    (a.mul b).index' q = max (a.index' q.1) (b.index' q.2) := by
  rw [Stream.index']
  split_ifs with h
  · simp at h; simp [index'_val' _ h.1, index'_val' _ h.2]; rfl
  · simp [-not_and, not_and_or] at h
    rcases h with h | h
    <;> simp [index'_invalid h]

theorem min_toOrder_le (a b : Stream ι α) (q) :
    min (a.toOrder (mul.valid.fst q)) (b.toOrder (mul.valid.snd q)) ≤ (a.mul b).toOrder q := by
  rw [Prod.Lex.le_iff'']
  simp only [Monotone.map_min (@Prod.Lex.fst_mono ι Bool _ _)]
  constructor
  · exact min_le_max
  · simp only [toOrder]
    aesop

theorem toOrder_le_max (a b : Stream ι α) (q) :
    (a.mul b).toOrder q ≤ max (a.toOrder <| mul.valid.fst q) (b.toOrder <| mul.valid.snd q) := by
  rw [Prod.Lex.le_iff']; right; constructor
  · simp [Monotone.map_max (@Prod.Lex.fst_mono ι Bool _ _)]
  · simp only [Bool.le_iff_imp, toOrder]
    aesop

instance Stream.mul.isBounded (a b : Stream ι α) [IsBounded a] [IsBounded b] :
    IsBounded (a.mul b) :=
  ⟨⟨Prod.rprodEq a.wfRel b.wfRel,
    fun q i => by
      rcases a.wf_valid (mul.valid.fst q) i with (h | ⟨ha₁, ha₂⟩)
      · left; left; exact ⟨h, b.no_backward ..⟩
      · rcases b.wf_valid (mul.valid.snd q) i with (h | ⟨hb₁, hb₂⟩)
        · left; right; exact ⟨h, a.no_backward ..⟩
        · right; constructor; swap
          · simp [ha₂, hb₂]
          · exact lt_of_lt_of_le (lt_min ha₁ hb₁) (min_toOrder_le ..)⟩⟩

theorem mul_map [Mul α] [Mul β] (a : Stream ι α) (b : Stream ι α) (f : α → β) (hf : ∀ x y, f (x * y) = (f x) * (f y)) :
    (a.mul b).map f = (a.map f).mul (b.map f) := by
  ext <;> try rfl
  simp only [heq_iff_eq]
  ext q₁
  simp [map, hf]
  rfl

end IndexLemmas

section ValueLemmas

variable [NonUnitalNonAssocSemiring α]

lemma mul_eval₀_of_neq {a : Stream ι α} {b : Stream ι α} (q)
    (h : a.toOrder (mul.valid.fst q) ≠ b.toOrder (mul.valid.snd q)) : (a.mul b).eval₀ q = 0 := by
  contrapose! h
  apply Stream.mul.ready.order_eq
  simp only [Stream.eval₀, Stream.mul_ready, Stream.mul_index, ge_iff_le, Stream.mul_value, ne_eq, dite_eq_right_iff,
    Finsupp.single_eq_zero, not_forall] at h
  exact h.fst

theorem mul_eval₀ (a b : Stream ι α) (q) :
    (a.mul b).eval₀ q = a.eval₀ (mul.valid.fst q) * b.eval₀ (mul.valid.snd q) := by
  rw [Stream.eval₀]; split_ifs with hr
  · simp only [mul_ready, Bool.and_eq_true, decide_eq_true_eq] at hr
    rcases hr with ⟨⟨hr₁, hr₂⟩, hr₃⟩
    simp [Stream.eval₀, hr₁, hr₂, hr₃]
    rfl
  · simp only [Stream.eval₀]
    split_ifs with h₁ h₂ <;> try simp
    simp only [mul_ready, h₁, h₂, Bool.and_self, Bool.true_and, decide_eq_true_eq] at hr
    rw [Finsupp.mul_single_eq_zero]
    assumption

theorem mul_eval₀_spec (a b : Stream ι α) [IsBounded a] [IsBounded b] (ha : a.IsStrictMono)
    (hb : b.IsStrictMono) (q) :
    (a.mul b).eval₀ q =
      (a.eval (mul.valid.fst q) * b.eval (mul.valid.snd q)).filter fun i => (i, false) <ₗ (a.mul b).toOrder q := by classical
  by_cases H : (a.mul b).ready q
  · calc
      (a.mul b).eval₀ q = a.eval₀ (mul.valid.fst q) * b.eval₀ (mul.valid.snd q) := mul_eval₀ ..
      _ = ((a.eval <| mul.valid.fst q).filter fun i => (i, false) <ₗ a.toOrder (mul.valid.fst q)) *
            ((b.eval <| mul.valid.snd q).filter fun i => (i, false) <ₗ b.toOrder (mul.valid.snd q)) :=
        by rw [ha.eval₀_eq_eval_filter, hb.eval₀_eq_eval_filter]
      _ = (a.eval (mul.valid.fst q) * b.eval (mul.valid.snd q)).filter fun i =>
            (i, false) <ₗ min (a.toOrder (mul.valid.fst q)) (b.toOrder (mul.valid.snd q)) :=
        by simp only [Finsupp.mul_filter, lt_min_iff]
      _ = (a.eval (mul.valid.fst q) * b.eval (mul.valid.snd q)).filter fun i => (i, false) <ₗ (a.mul b).toOrder q :=
        by simp [order_eq_of_mul_ready H]
  · symm
    simp only [Stream.eval₀, H, dite_false, coe_mul_valid_fst,
      mul.valid, coe_mul_valid_snd, Finsupp.filter_eq_zero_iff]
    intro i hi
    simp only [Stream.toOrder, H, mul_index, Prod.Lex.mk_snd_mono_lt_iff, lt_max_iff] at hi
    refine
        mul_eq_zero_of
          (hi.imp (fun h => ha.1.eq_zero_of_lt_index i ?_) fun h =>
            hb.1.eq_zero_of_lt_index i ?_) <;>
      rwa [Stream.index'_val', WithTop.coe_lt_coe]

theorem mul_mono {a b : Stream ι α} (ha : a.IsMonotonic) (hb : b.IsMonotonic) :
    (a.mul b).IsMonotonic := by
  intro q i
  simp only [Stream.mul_index']
  exact max_le_max (ha _ _) (hb _ _)

theorem mul_strict_mono {a b : Stream ι α} (ha : a.IsStrictMono) (hb : b.IsStrictMono) :
    (a.mul b).IsStrictMono where
  left := mul_mono ha.1 hb.1
  right q i H hr :=
    ne_of_lt (by
      simp only [Stream.mul_index']
      have := order_eq_of_mul_ready hr
      simp at hr
      apply max_lt_max (ha.lt (hr := hr.1.1) ..) (hb.lt (hr := hr.1.2) ..) <;>
        simpa [this])

theorem next_eval_mul_eq (a b : Stream ι α) [IsStrictLawful a] [IsStrictLawful b] (q : {q // (a.mul b).valid q}) :
    a.eval ((a.mul b).advance q).1 * b.eval ((a.mul b).advance q).2 =
      (a.eval (mul.valid.fst q) * b.eval (mul.valid.snd q)).filter fun i => (a.mul b).toOrder q ≤ (i, false) := by
  ext j
  simp only [Finsupp.mul_apply, Finsupp.filter_apply, Stream.advance_val]
  split_ifs with hj
  · simp only [Stream.toOrder, Stream.index'_val, Stream.mul_seek] at hj ⊢
    rw [IsLawful.skip_spec (mul.valid.fst q) _ _ hj, IsLawful.skip_spec (mul.valid.snd q) _ _ hj]
  · dsimp only [mul_seek]
    rw [not_le] at hj
    rcases le_max_iff.mp <| toOrder_le_max a b q with hj' | hj'
    · rw [a.strictMono.eval_skip_eq_zero, MulZeroClass.zero_mul] <;> assumption
    · rw [b.strictMono.eval_skip_eq_zero, MulZeroClass.mul_zero] <;> assumption


theorem mul_spec (a b : Stream ι α) [IsStrictLawful a] [IsStrictLawful b] (q : (a.mul b).σ) :
    (a.mul b).eval q = a.eval q.1 * b.eval q.2 := by
  apply (a.mul b).wf.induction q
  clear q; intro q ih
  by_cases hv : (a.mul b).valid q; swap
  · have := hv
    simp only [mul_valid, Bool.and_eq_true, not_and_or, Bool.not_eq_true] at hv
    rcases hv with hv' | hv' <;> simp [this, hv']
  · rw [Stream.eval_valid _ ⟨_, hv⟩, ih _ ((a.mul b).next_wf ⟨q, hv⟩), next_eval_mul_eq _ _ ⟨_, hv⟩,
      mul_eval₀_spec _ _ a.strictMono b.strictMono ⟨_, hv⟩]
    convert Finsupp.filter_pos_add_filter_neg (α := ι) (M := α) ..
    simp

theorem mul_skip_spec (a b : Stream ι α) [IsStrictLawful a] [IsStrictLawful b] (q : {q // (a.mul b).valid q})
    (i : ι ×ₗ Bool) (j : ι) (h : i ≤ₗ (j, false)) :
    (a.mul b).eval ((a.mul b).seek q i) j = (a.mul b).eval q j := by
  simp only [Finsupp.mul_apply, mul_spec]
  congr 1 <;> dsimp <;> rw [IsLawful.skip_spec] <;> aesop

instance (a b : Stream ι α) [IsStrictLawful a] [IsStrictLawful b] :
    IsStrictLawful (a.mul b) where
  skip_spec := mul_skip_spec a b
  strictMono := mul_strict_mono a.strictMono b.strictMono


end ValueLemmas

end Etch.Verification.Stream
