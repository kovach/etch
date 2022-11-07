import tactic
import data.finsupp.basic
import control.bifunctor
import verification.misc
import verification.stream_props

open_locale classical
noncomputable theory

variables {σ₁ σ₂ α ι : Type}
[linear_order ι]
[non_unital_non_assoc_semiring α]

@[mk_iff]
structure Stream.mul.ready (a : Stream σ₁ ι α) (b : Stream σ₂ ι α) (s : σ₁ × σ₂) : Prop :=
(v₁ : a.valid s.1)
(v₂ : b.valid s.2)
(r₁ : a.ready s.1)
(r₂ : b.ready s.2)
(index : a.index s.1 v₁ = b.index s.2 v₂)

@[simps]
def Stream.mul (a : Stream σ₁ ι α) (b : Stream σ₂ ι α) : Stream (σ₁ × σ₂) ι α :=
{ valid := λ p, a.valid p.1 ∧ b.valid p.2,
  ready := λ p, Stream.mul.ready a b p,
  next  := λ p hv, if a.to_order p.1 ≤ b.to_order p.2 then (a.next p.1 hv.1, p.2) else (p.1, b.next p.2 hv.2),
  index := λ p hv, max (a.index p.1 hv.1) (b.index p.2 hv.2),
  value := λ p hr, a.value p.1 hr.r₁ * b.value p.2 hr.r₂ }

infixl ` ⋆ `:71 := Stream.mul

section lemmas

lemma Stream.mul.ready.index' {a : Stream σ₁ ι α} {b : Stream σ₂ ι α} {x y} (h : (a ⋆ b).ready (x, y)) :
  a.index' x = b.index' y :=
by simp [Stream.index'_val h.v₁, Stream.index'_val h.v₂, h.index]

lemma Stream.mul.ready.order_eq {a : Stream σ₁ ι α} {b : Stream σ₂ ι α} {x y} (h : (a ⋆ b).ready (x, y)) :
  a.to_order x = b.to_order y :=
by ext : 1; simp [h.r₁, h.r₂, h.index']

lemma Stream.mul_eval₀_of_neq {a : Stream σ₁ ι α} {b : Stream σ₂ ι α} {x y} (h : a.to_order x ≠ b.to_order y) (H) :
  (a ⋆ b).eval₀ (x, y) H = 0 :=
by { contrapose! h, apply Stream.mul.ready.order_eq, simp [Stream.eval₀] at h, exact h.fst, }

lemma Stream.mul_eval₀ (a : Stream σ₁ ι α) (b : Stream σ₂ ι α) (x : σ₁) (y : σ₂) (H) :
  (a ⋆ b).eval₀ (x, y) H = (a.eval₀ x H.1) * (b.eval₀ y H.2) :=
begin
  rw [Stream.eval₀], split_ifs with hr,
  { simp [Stream.eval₀, hr.r₁, hr.r₂, hr.index], },
  simp [Stream.mul.ready_iff, H.1, H.2] at hr,
  simp [Stream.eval₀], split_ifs with h₁ h₂; try { simp },
  rw finsupp.mul_single_eq_zero _ _ (hr h₁ h₂),
end

lemma Stream.mul_index' (a : Stream σ₁ ι α) (b : Stream σ₂ ι α) (xy : σ₁ × σ₂) :
  (a ⋆ b).index' xy = max (a.index' xy.1) (b.index' xy.2) :=
begin
  cases xy with x y,
  rw [Stream.index'], simp, split_ifs with h,
  { simp [Stream.index'_val h.1, Stream.index'_val h.2], },
  rw not_and_distrib at h, cases h; simp [Stream.index'_invalid h],
end

/-- This lemma states that if `a.to_order x ≤ b.to_order y`, 
  then the support of `a.eval₀ x h₁` (which is at most `{a.index x}`) 
  is disjoint from `b.eval_steps n (b.next y)`, assuming `b` is simple. -/
lemma Stream.mul_eq_zero_aux {a : Stream σ₁ ι α} {b : Stream σ₂ ι α} (hb : b.simple) {x : σ₁} {y : σ₂}
  (h₁ : a.valid x) (h₂ : b.valid y) (H : a.to_order x ≤ b.to_order y) (n : ℕ) :
  disjoint (a.eval₀ x h₁).support (b.eval_steps n (b.next y h₂)).support :=
begin
  -- Assume `a` is ready, or else `a.eval₀ x h₁ = 0` has trivial support.
  by_cases hr : a.ready x, swap, { simp [Stream.eval₀, hr], },
  rw finset.disjoint_iff_ne,
  intros i₁ hi₁ i₂ hi₂,
  cases finset.mem_singleton.mp (a.eval₀_support _ _ hi₁),
  rw le_iff_eq_or_lt at H,
  refine ne_of_lt (with_top.coe_lt_coe.mp _), rw ← Stream.index'_val h₁,
  cases H,
  { -- `a.to_order x = b.to_order y`
    simp [prod.ext_iff, hr] at H,
    rw H.1,
    exact hb.index_lt_support h₂ H.2 _ hi₂, },
  -- Case `a < b`
  refine lt_of_lt_of_le (prod.lex.fst_lt_of_lt_of_le H (by simp [hr])) _,
  exact (hb.monotonic h₂).trans (hb.monotonic.index_le_support _ hi₂),
end

lemma Stream.mul_eq_zero {a : Stream σ₁ ι α} {b : Stream σ₂ ι α} (hb : b.simple) {x : σ₁} {y : σ₂}
  (h₁ : a.valid x) (h₂ : b.valid y) (H : a.to_order x ≤ b.to_order y) (n : ℕ) :
  a.eval₀ x h₁ * b.eval_steps n (b.next y h₂) = 0 :=
by { rw [finsupp.mul_eq_zero_of_disjoint_support], exact Stream.mul_eq_zero_aux hb h₁ h₂ H n, }

lemma Stream.mul_eq_zero' {a : Stream σ₁ ι α} {b : Stream σ₂ ι α} (ha : a.simple) {x : σ₁} {y : σ₂}
  (h₁ : a.valid x) (h₂ : b.valid y) (H : b.to_order y ≤ a.to_order x) (n : ℕ) :
  a.eval_steps n (a.next x h₁) * b.eval₀ y h₂ = 0 :=
by { rw [finsupp.mul_eq_zero_of_disjoint_support], exact (Stream.mul_eq_zero_aux ha h₂ h₁ H n).symm, }

end lemmas

theorem Stream.mul_spec_aux {a : Stream σ₁ ι α} {b : Stream σ₂ ι α} (hsa : a.simple) (hsb : b.simple) (n : ℕ)
  {x y B₁ B₂} (ha : a.bound_valid B₁ x) (hb : b.bound_valid B₂ y) (hn : n = B₁ + B₂) :
  ∃ (k₁ k₂ : ℕ), k₁ ≤ B₁ ∧ k₂ ≤ B₂ ∧ n = k₁ + k₂ ∧ 
    (a ⋆ b).eval_steps n (x, y) = (a.eval_steps k₁ x) * (b.eval_steps k₂ y) ∧
    ((a ⋆ b).valid ((a ⋆ b).next'^[n] (x, y)) → ((a ⋆ b).next'^[n] (x, y)) = (a.next'^[k₁] x, b.next'^[k₂] y)) :=
begin
  induction n with n ih generalizing B₁ B₂ x y,
  { use [0, 0], simp, },
  by_cases H : (a ⋆ b).valid (x, y), swap,
  { simp only [Stream.eval_invalid H, Stream.next'_val_invalid' H],
    refine ⟨B₁, B₂, rfl.le, rfl.le, hn, _, false.elim ∘ H⟩,
    cases (show ¬a.valid x ∨ ¬b.valid y, by simpa [not_and_distrib] using H) with h;
    simp [Stream.eval_invalid h], },
  cases B₁, { cases H.1.bound_pos ha, },
  cases B₂, { cases H.2.bound_pos hb, },
  simp [nat.succ_eq_add_one, ← add_assoc] at hn,
  by_cases h : a.to_order x ≤ b.to_order y,
  { -- Advance `a` (i.e. `a ≤ b`)
    rw [Stream.bound_valid_succ] at ha,
    obtain ⟨k₁, k₂, hk₁, hk₂, rfl, he, hiter⟩ := ih (ha H.1) hb (hn.trans (add_right_comm _ _ _)),
    refine ⟨k₁ + 1, k₂, nat.succ_le_succ hk₁, hk₂, (add_right_comm k₁ k₂ 1), _, _⟩,
    { simp [H, H.1, h, he, add_mul], congr, 
      cases k₂, { exfalso, linarith only [hn, hk₁], },
      simp [H.2, mul_add, Stream.mul_eq_zero hsb H.1 H.2 h, Stream.mul_eval₀], },
    simp only [Stream.next'_val H, function.iterate_succ_apply, Stream.mul_next, h, if_true, Stream.next'_val H.1],
    exact hiter, },
  { -- Advance `b` (i.e. `b < a`)
    push_neg at h,
    rw [Stream.bound_valid_succ] at hb,
    obtain ⟨k₁, k₂, hk₁, hk₂, rfl, he, hiter⟩ := ih ha (hb H.2) hn,
    refine ⟨k₁, k₂ + 1, hk₁, nat.succ_le_succ  hk₂, rfl, _, _⟩,
    { simp [H, H.2, h.not_le, he, mul_add], congr,
      cases k₁, { exfalso, linarith only [hn, hk₂], },
      simp [H.1, add_mul, Stream.mul_eval₀, Stream.mul_eq_zero' hsa H.1 H.2 h.le], },
    simp only [Stream.next'_val H, function.iterate_succ_apply, Stream.mul_next, h.not_le, if_false, Stream.next'_val H.2],
    exact hiter, }
end

lemma Stream.mul_spec {a : Stream σ₁ ι α} {b : Stream σ₂ ι α} (hsa : a.simple) (hsb : b.simple)
  {x y B₁ B₂} (ha : a.bound_valid B₁ x) (hb : b.bound_valid B₂ y) :
  (a ⋆ b).eval_steps (B₁ + B₂) (x, y) = (a.eval_steps B₁ x) * (b.eval_steps B₂ y) ∧ 
  ((a ⋆ b).valid ((a ⋆ b).next'^[B₁ + B₂] (x, y)) → ((a ⋆ b).next'^[B₁ + B₂] (x, y) = (a.next'^[B₁] x, b.next'^[B₂] y))) :=
begin
  obtain ⟨k₁, k₂, hk₁, hk₂, hs, he, hiter⟩ := Stream.mul_spec_aux hsa hsb (B₁ + B₂) ha hb rfl,
  obtain ⟨rfl, rfl⟩ : k₁ = B₁ ∧ k₂ = B₂ := by split; linarith only [hk₁, hk₂, hs],
  exact ⟨he, hiter⟩,
end

@[simps]
def StreamExec.mul (a : StreamExec σ₁ ι α) (b : StreamExec σ₂ ι α) : StreamExec (σ₁ × σ₂) ι α :=
{ stream := a.stream ⋆ b.stream,
  state := (a.state, b.state),
  bound := a.bound + b.bound }

infixl ` ⋆ `:71 := StreamExec.mul


lemma StreamExec.mul_bound_valid {a : StreamExec σ₁ ι α} {b : StreamExec σ₂ ι α} (hsa : a.stream.simple) (hsb : b.stream.simple)
  (ha : a.bound_valid) (hb : b.bound_valid) :
  (a ⋆ b).bound_valid :=
begin
  rw [StreamExec.bound_valid, bound_valid_iff_next'_iterate],
  intro H,
  have := (Stream.mul_spec hsa hsb ha hb).2 H,
  simp [this] at H,
  rw [StreamExec.bound_valid, bound_valid_iff_next'_iterate] at ha,
  exact absurd H.1 ha,
end

@[simp] lemma StreamExec.mul_spec {a : StreamExec σ₁ ι α} {b : StreamExec σ₂ ι α} (hsa : a.stream.simple) (hsb : b.stream.simple) 
  (ha : a.bound_valid) (hb : b.bound_valid) :
  (a ⋆ b).eval = a.eval * b.eval :=  (Stream.mul_spec hsa hsb ha hb).1

lemma Stream.mul_is_monotonic {a : Stream σ₁ ι α} {b : Stream σ₂ ι α} (hsa : a.monotonic) (hsb : b.monotonic) :
  (a ⋆ b).monotonic :=
begin
  rintros ⟨x, y⟩ H,
  simp only [Stream.mul_index'],
  refine max_le_max _ _; simp; split_ifs,
  any_goals { exact rfl.le, },
  exacts [hsa _, hsb _],
end

lemma Stream.mul_is_simple {a : Stream σ₁ ι α} {b : Stream σ₂ ι α} (hsa : a.simple) (hsb : b.simple) :
  (a ⋆ b).simple :=
begin
  refine ⟨Stream.mul_is_monotonic hsa.monotonic hsb.monotonic, _⟩,
  rintros ⟨x, y⟩ hv hr,
  simp only [Stream.mul_index', hr.index', max_self, Stream.mul_next],
  split_ifs with H,
  { simp only [← hr.index', ne, max_ne_self_iff'], exact hsa.index_lt_next _ hr.r₁, },
  { simp only [hr.index', ne, max_ne_self_iff], exact hsb.index_lt_next _ hr.r₂, },
end


