import Etch.StreamFusion.Proofs.StreamProof
import Etch.StreamFusion.Multiply

namespace Etch.Verification.Stream

open Streams

universe u
variable {ι : Type} [LinearOrder ι] {α : Type u}

section IndexLemmas

variable [Mul α]

theorem Stream.mul.ready.order_eq {a : Stream ι α} {b : Stream ι α} {q}
    (h : mul.ready a b q) : a.toOrder (mul.valid.fst q) = b.toOrder (mul.valid.snd q) := by
  dsimp only [Stream.toOrder]
  aesop

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

end ValueLemmas

#exit

theorem mul_eval₀_spec (a b : Stream ι α) [IsBounded a] [IsBounded b] (ha : a.IsStrictMono)
    (hb : b.IsStrictMono) (q : (a.mul b).σ) (hv : (a.mul b).valid q) :
    (a.mul b).eval₀ q hv =
      (a.eval q.1 * b.eval q.2).filter fun i => (i, false) <ₗ (a.mul b).toOrder q hv := by classical
  by_cases H : (a.mul b).ready q
  · rcases q with ⟨qa, qb⟩
    calc
      (a.mul b).eval₀ (qa, qb) hv = a.eval₀ qa hv.1 * b.eval₀ qb hv.2 := by
        dsimp
        rw [mul_eval₀]
      _ = ((a.eval qa).filter fun i => (i, false) <ₗ a.toOrder qa hv.1) *
            ((b.eval qb).filter fun i => (i, false) <ₗ b.toOrder qb hv.2) :=
        by rw [ha.eval₀_eq_eval_filter, hb.eval₀_eq_eval_filter]
      _ = (a.eval qa * b.eval qb).filter fun i =>
            (i, false) <ₗ min (a.toOrder qa hv.1) (b.toOrder qb hv.2) :=
        by simp only [Finsupp.mul_filter, lt_min_iff]
      _ = (a.eval qa * b.eval qb).filter fun i => (i, false) <ₗ (a.mul b).toOrder (qa, qb) hv :=
        by
          congr
          ext i
          simp [(order_eq_of_mul_ready H).1, (order_eq_of_mul_ready H).2]

  · symm
    simp only [Stream.eval₀, H, dif_neg, not_false_iff, Finsupp.filter_eq_zero_iff,
      Stream.toOrder, decide_False', Prod.Lex.mk_snd_mono_lt_iff, Finsupp.mul_apply,
      Stream.mul_index, lt_max_iff]
    intro i hi
    refine
        mul_eq_zero_of
          (hi.imp (fun h => ha.1.eq_zero_of_lt_index i ?_) fun h =>
            hb.1.eq_zero_of_lt_index i ?_) <;>
      simpa [hv.1, hv.2] using h
#align mul_eval₀_spec Etch.Verification.mul_eval₀_spec

theorem mul_mono {a b : Stream ι α} (ha : a.IsMonotonic) (hb : b.IsMonotonic) :
    (a.mul b).IsMonotonic := by
  intro q hv i
  simp only [Stream.mul_index']
  exact max_le_max (ha _ _ _) (hb _ _ _)
#align mul_mono Etch.Verification.mul_mono

theorem mul_strict_mono {a b : Stream ι α} (ha : a.IsStrictMono) (hb : b.IsStrictMono) :
    (a.mul b).IsStrictMono where
  left := mul_mono ha.1 hb.1
  right q hv i H hr :=
    ne_of_lt
      (by
        simp only [Stream.mul_index']
        rcases q with ⟨qa, qb⟩
        apply max_lt_max (ha.lt (hr := hr.r₁) ..) (hb.lt (hr := hr.r₂) ..) <;>
          simpa [order_eq_of_mul_ready hr])
#align mul_strict_mono Etch.Verification.mul_strict_mono

theorem next_eval_mul_eq (a b : Stream ι α) [IsStrictLawful a] [IsStrictLawful b] (q : (a.mul b).σ)
    (hv : (a.mul b).valid q) :
    a.eval ((a.mul b).next q).1 * b.eval ((a.mul b).next q).2 =
      (a.eval q.1 * b.eval q.2).filter fun i => (a.mul b).toOrder q hv ≤ (i, false) := by
  ext j
  simp only [Finsupp.mul_apply, Finsupp.filter_apply, Stream.next_val hv]
  split_ifs with hj
  · simp only [Stream.toOrder, Stream.index'_val hv, Stream.mul_skip] at hj ⊢
    rw [IsLawful.skip_spec q.1 hv.1 _ _ hj, IsLawful.skip_spec q.2 hv.2 _ _ hj]
  · change a.eval (a.skip ..) j * b.eval (b.skip ..) j = 0
    rw [not_le] at hj
    rcases le_max_iff.mp <| toOrder_le_max _ _ _ hv with hj' | hj'
    · rw [a.strictMono.eval_skip_eq_zero, MulZeroClass.zero_mul] <;> assumption
    · rw [b.strictMono.eval_skip_eq_zero, MulZeroClass.mul_zero] <;> assumption
#align next_eval_mul_eq Etch.Verification.next_eval_mul_eq

theorem mul_spec (a b : Stream ι α) [IsStrictLawful a] [IsStrictLawful b] (q : (a.mul b).σ) :
    (a.mul b).eval q = a.eval q.1 * b.eval q.2 := by
  apply (a.mul b).wf.induction q
  clear q; intro q ih
  by_cases hv : (a.mul b).valid q; swap
  · rcases not_and_or.mp hv with hv' | hv' <;> simp [hv, hv']
  · rw [Stream.eval_valid _ _ hv, ih _ ((a.mul b).next_wf q hv), next_eval_mul_eq _ _ _ hv,
      mul_eval₀_spec _ _ a.strictMono b.strictMono _ hv]
    convert Finsupp.filter_pos_add_filter_neg (α := ι) (M := α) ..
    simp
#align mul_spec Etch.Verification.mul_spec

theorem mul_skip_spec (a b : Stream ι α) [IsStrictLawful a] [IsStrictLawful b] (q : (a.mul b).σ)
    (hq : (a.mul b).valid q) (i : ι ×ₗ Bool) (j : ι) (h : i ≤ₗ (j, false)) :
    (a.mul b).eval ((a.mul b).skip q hq i) j = (a.mul b).eval q j := by
  simp only [Finsupp.mul_apply, mul_spec];
  congr 1 <;> dsimp <;> rwa [IsLawful.skip_spec]
#align mul_skip_spec Etch.Verification.mul_skip_spec

instance (a b : Stream ι α) [IsStrictLawful a] [IsStrictLawful b] :
    IsStrictLawful (a.mul b) where
  skip_spec := mul_skip_spec a b
  strictMono := mul_strict_mono a.strictMono b.strictMono

end ValueLemmas


end Etch.Verification
