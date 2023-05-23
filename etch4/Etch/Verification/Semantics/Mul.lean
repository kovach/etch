import Etch.Verification.Semantics.SkipStream

/-!
# Multiplication of indexed streams

In this file, we define the product of indexed streams `Stream.mul`.

## Main results
  - `mul_spec`: States that `(a.mul b).eval q = (a.eval q) * (b.eval q)` i.e.
      multiply does what it says it does, assuming `a` and `b` are strictly lawful.
  - `is_strict_lawful (a.mul b)`: The product stream is strictly lawful assuming `a` and `b` are.
-/

set_option linter.uppercaseLean3 false

namespace Etch.Verification

open Classical
open Streams

universe u
variable {ι : Type} [LinearOrder ι] {α : Type u}

@[mk_iff]
structure Stream.mul.Ready {ι : Type} (a : Stream ι α) (b : Stream ι α) (s : a.σ × b.σ) : Prop where
  v₁ : a.valid s.1
  v₂ : b.valid s.2
  r₁ : a.ready s.1
  r₂ : b.ready s.2
  index : a.index s.1 v₁ = b.index s.2 v₂
#align Stream.mul.ready Etch.Verification.Stream.mul.Ready

@[simps]
def Stream.mul [Mul α] (a b : Stream ι α) : Stream ι α
    where
  σ := a.σ × b.σ
  valid p := a.valid p.1 ∧ b.valid p.2
  ready p := Stream.mul.Ready a b p
  skip p hp i := (a.skip p.1 hp.1 i, b.skip p.2 hp.2 i)
  index p hv := max (a.index p.1 hv.1) (b.index p.2 hv.2)
  value p hr := a.value p.1 hr.r₁ * b.value p.2 hr.r₂
#align Stream.mul Etch.Verification.Stream.mul

section IndexLemmas

variable [Mul α]

theorem Stream.mul.ready.index' {a : Stream ι α} {b : Stream ι α} {x y}
    (h : (a.mul b).ready (x, y)) : a.index' x = b.index' y := by
  rw [Stream.index'_val h.v₁, Stream.index'_val h.v₂]
  simpa using h.index
#align Stream.mul.ready.index' Etch.Verification.Stream.mul.ready.index'

theorem Stream.mul.ready.order_eq {a : Stream ι α} {b : Stream ι α} {x y}
    (h : (a.mul b).ready (x, y)) : a.toOrder x h.v₁ = b.toOrder y h.v₂ := by
  dsimp only [Stream.toOrder]
  congr 1
  · exact h.index
  · have r₁ := h.r₁; dsimp only at r₁
    have r₂ := h.r₂; dsimp only at r₂
    simp [*]
#align Stream.mul.ready.order_eq Etch.Verification.Stream.mul.ready.order_eq

theorem Stream.mul_index' (a b : Stream ι α) (xy : a.σ × b.σ) :
    (a.mul b).index' xy = max (a.index' xy.1) (b.index' xy.2) := by
  rcases xy with ⟨x, y⟩
  rw [Stream.index']
  simp only [Stream.mul_index, WithTop.coe_max]
  split_ifs with h
  · rw [Stream.index'_val h.1, Stream.index'_val h.2]
  · erw [not_and_or] at h
    rcases h with h | h <;> (rw [Stream.index'_invalid h]; simp)
#align Stream.mul_index' Etch.Verification.Stream.mul_index'

theorem order_eq_of_mul_ready {a b : Stream ι α} {x y} (h : (a.mul b).ready (x, y)) :
    a.toOrder x h.v₁ = (a.mul b).toOrder (x, y) ⟨h.v₁, h.v₂⟩ ∧
      b.toOrder y h.v₂ = (a.mul b).toOrder (x, y) ⟨h.v₁, h.v₂⟩ := by
  dsimp only [Stream.mul_ready] at h
  have := h.index; have := h.r₁; have := h.r₂; dsimp only at *
  constructor <;> simp [Stream.toOrder, *]
#align order_eq_of_mul_ready Etch.Verification.order_eq_of_mul_ready

/-- This lemma takes a surprising amount of effort to prove -/
theorem min_toOrder_le (a b : Stream ι α) (q : a.σ × b.σ) (hv : (a.mul b).valid q) :
    min (a.toOrder q.1 hv.1) (b.toOrder q.2 hv.2) ≤ (a.mul b).toOrder q hv := by
  rw [Prod.Lex.le_iff'']
  simp only [Monotone.map_min (@Prod.Lex.fst_mono ι Bool _ _)]
  constructor
  · exact min_le_max
  · intro h
    simp only [Stream.toOrder_fst, Stream.mul_index, max_eq_min_iff] at h
    suffices a.ready q.1 → b.ready q.2 → (a.mul b).ready q by
      simpa [Stream.toOrder, h, Prod.Lex.mk_min, Bool.min_eq_and, Bool.le_iff_imp]
    intro hr₁ hr₂
    refine ⟨hv.1, hv.2, hr₁, hr₂, ?_⟩
    simpa [hv.1, hv.2] using h
#align min_to_order_le Etch.Verification.min_toOrder_le

theorem toOrder_le_max (a b : Stream ι α) (q : a.σ × b.σ) (hv : (a.mul b).valid q) :
    (a.mul b).toOrder q hv ≤ max (a.toOrder q.1 hv.1) (b.toOrder q.2 hv.2) := by
  rw [Prod.Lex.le_iff']; right; constructor
  · simp [Monotone.map_max (@Prod.Lex.fst_mono ι Bool _ _), Stream.mul_index']
  simp only [Bool.le_iff_imp, Stream.toOrder_snd, Bool.of_decide_iff]
  intro hr; rcases q with ⟨qa, qb⟩
  simpa [order_eq_of_mul_ready hr]
#align to_order_le_max Etch.Verification.toOrder_le_max

instance Stream.mul.isBounded (a b : Stream ι α) [IsBounded a] [IsBounded b] :
    IsBounded (a.mul b) :=
  ⟨⟨Prod.rprodEq a.wfRel b.wfRel,
    fun q hq i => by
      rcases a.wf_valid q.1 hq.1 i with (h | ⟨ha₁, ha₂⟩)
      · left; left; exact ⟨h, b.no_backward ..⟩
      · rcases b.wf_valid q.2 hq.2 i with (h | ⟨hb₁, hb₂⟩)
        · left; right; exact ⟨h, a.no_backward ..⟩
        · right; constructor; swap
          · simp [ha₂, hb₂]
          · exact lt_of_lt_of_le (lt_min ha₁ hb₁) (min_toOrder_le (hv := hq) ..)⟩⟩
#align Stream.mul.is_bounded Etch.Verification.Stream.mul.isBounded

theorem Stream.mul_map {β : Type _} [Mul β] (f : α → β) (f_mul : ∀ x y, f (x * y) = f x * f y)
    (q r : Stream ι α) : (q.mul r).map f = (q.map f).mul (r.map f) := by
  ext <;> solve_refl
  · simp only [Stream.mul.Ready_iff]; rfl
  · simp only [f_mul, apply_ite f]
#align Stream.mul_map Etch.Verification.Stream.mul_map

end IndexLemmas

section ValueLemmas

variable [NonUnitalNonAssocSemiring α]

theorem mul_eval₀_of_neq {a : Stream ι α} {b : Stream ι α} {x y} (H : (a.mul b).valid (x, y))
    (h : a.toOrder x H.1 ≠ b.toOrder y H.2) : (a.mul b).eval₀ (x, y) H = 0 := by
  contrapose! h
  apply Stream.mul.ready.order_eq
  simp [Stream.eval₀] at h
  exact h.fst
#align mul_eval₀_of_neq Etch.Verification.mul_eval₀_of_neq

theorem mul_eval₀ (a b : Stream ι α) (x : a.σ) (y : b.σ) (H) :
    (a.mul b).eval₀ (x, y) H = a.eval₀ x H.1 * b.eval₀ y H.2 := by
  rw [Stream.eval₀]; split_ifs with hr
  · obtain ⟨v₁, v₂, r₁, r₂, hi⟩ := hr; dsimp only at v₁ v₂ r₁ r₂ hi
    simp [Stream.eval₀, *]
  · simp [Stream.mul.Ready_iff, H.1, H.2] at hr
    simp [Stream.eval₀]
    split_ifs with h₁ h₂ <;> try simp
    rw [Finsupp.mul_single_eq_zero _ _ (hr h₁ h₂ H.1 H.2)]
#align mul_eval₀ Etch.Verification.mul_eval₀

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
