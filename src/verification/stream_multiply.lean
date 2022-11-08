import tactic
import data.finsupp.basic
import control.bifunctor
import verification.misc
import verification.stream_props
import verification.finsuppeval

open_locale classical
noncomputable theory

variables {ι : Type} {α : Type*}
[linear_order ι]

@[mk_iff]
structure Stream.mul.ready {ι : Type} (a : Stream ι α) (b : Stream ι α) (s : a.σ × b.σ) : Prop :=
(v₁ : a.valid s.1)
(v₂ : b.valid s.2)
(r₁ : a.ready s.1)
(r₂ : b.ready s.2)
(index : a.index s.1 v₁ = b.index s.2 v₂)

section defs
variables [has_mul α]

@[simps]
instance : has_mul (Stream ι α) := ⟨λ a b,
{ σ := a.σ × b.σ,
  valid := λ p, a.valid p.1 ∧ b.valid p.2,
  ready := λ p, Stream.mul.ready a b p,
  next  := λ p hv, if a.to_order p.1 ≤ b.to_order p.2 then (a.next p.1 hv.1, p.2) else (p.1, b.next p.2 hv.2),
  index := λ p hv, max (a.index p.1 hv.1) (b.index p.2 hv.2),
  value := λ p hr, a.value p.1 hr.r₁ * b.value p.2 hr.r₂ }⟩

end defs


section index_lemmas
variables [has_mul α]

lemma Stream.mul.ready.index' {a : Stream ι α} {b : Stream ι α} {x y} (h : (a * b).ready (x, y)) :
  a.index' x = b.index' y :=
by simp [Stream.index'_val h.v₁, Stream.index'_val h.v₂, h.index]

lemma Stream.mul.ready.order_eq {a : Stream ι α} {b : Stream ι α} {x y} (h : (a * b).ready (x, y)) :
  a.to_order x = b.to_order y :=
by ext : 1; simp [h.r₁, h.r₂, h.index']

lemma Stream.mul_index' (a : Stream ι α) (b : Stream ι α) (xy : a.σ × b.σ) :
  (a * b).index' xy = max (a.index' xy.1) (b.index' xy.2) :=
begin
  cases xy with x y,
  rw [Stream.index'], simp, split_ifs with h,
  { simp [Stream.index'_val h.1, Stream.index'_val h.2], },
  rw not_and_distrib at h, cases h; simp [Stream.index'_invalid h],
end

end index_lemmas

section value_lemmas

variables [non_unital_non_assoc_semiring α]

lemma Stream.mul_eval₀_of_neq {a : Stream ι α} {b : Stream ι α} {x y} (h : a.to_order x ≠ b.to_order y) (H) :
  (a * b).eval₀ (x, y) H = 0 :=
by { contrapose! h, apply Stream.mul.ready.order_eq, simp [Stream.eval₀] at h, exact h.fst, }

lemma Stream.mul_eval₀ (a : Stream ι α) (b : Stream ι α) (x : a.σ) (y : b.σ) (H) :
  (a * b).eval₀ (x, y) H = (a.eval₀ x H.1) * (b.eval₀ y H.2) :=
begin
  rw [Stream.eval₀], split_ifs with hr,
  { simp [Stream.eval₀, hr.r₁, hr.r₂, hr.index], },
  simp [Stream.mul.ready_iff, H.1, H.2] at hr,
  simp [Stream.eval₀], split_ifs with h₁ h₂; try { simp },
  rw finsupp.mul_single_eq_zero _ _ (hr h₁ h₂),
end

/-- This lemma states that if `a.to_order x ≤ b.to_order y`, 
  then the support of `a.eval₀ x h₁` (which is at most `{a.index x}`) 
  is disjoint from `b.eval_steps n (b.next y)`, assuming `b` is simple. -/
lemma Stream.mul_eq_zero_aux {a : Stream ι α} {b : Stream ι α} (hb : b.simple) {x : a.σ} {y : b.σ}
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

lemma Stream.mul_eq_zero {a : Stream ι α} {b : Stream ι α} (hb : b.simple) {x : a.σ} {y : b.σ}
  (h₁ : a.valid x) (h₂ : b.valid y) (H : a.to_order x ≤ b.to_order y) (n : ℕ) :
  a.eval₀ x h₁ * b.eval_steps n (b.next y h₂) = 0 :=
by { rw [finsupp.mul_eq_zero_of_disjoint_support], exact Stream.mul_eq_zero_aux hb h₁ h₂ H n, }

lemma Stream.mul_eq_zero' {a : Stream ι α} {b : Stream ι α} (ha : a.simple) {x : a.σ} {y : b.σ}
  (h₁ : a.valid x) (h₂ : b.valid y) (H : b.to_order y ≤ a.to_order x) (n : ℕ) :
  a.eval_steps n (a.next x h₁) * b.eval₀ y h₂ = 0 :=
by { rw [finsupp.mul_eq_zero_of_disjoint_support], exact (Stream.mul_eq_zero_aux ha h₂ h₁ H n).symm, }

end value_lemmas


@[elab_as_eliminator]
theorem Stream.mul_induction [has_mul α] {a : Stream ι α} {b : Stream ι α} {x : a.σ} {y : b.σ}
  {B₁ B₂ : ℕ} (ha : a.bound_valid B₁ x) (hb : b.bound_valid B₂ y)
  (P : ∀ (x : a.σ) (y : b.σ) (k₁ : ℕ) (k₂ : ℕ) (N : ℕ), Prop)
  (hP_base : ∀ (x y), P x y 0 0 0)
  (hP_invalid : ∀ (x y B₁ B₂ N) (H : ¬(a * b).valid (x, y)) (hvx : ¬a.valid x ∨ ¬b.valid y), a.bound_valid B₁ x → b.bound_valid B₂ y → P x y B₁ B₂ N)
  (hP_advance_a : ∀ (x y k₁ k₂ N) (H : (a * b).valid (x, y)), a.to_order x ≤ b.to_order y → P (a.next x H.1) y k₁ (k₂ + 1) N → P x y (k₁ + 1) (k₂ + 1) (N + 1))
  (hP_advance_b : ∀ (x y k₁ k₂ N) (H : (a * b).valid (x, y)), b.to_order y < a.to_order x → P x (b.next y H.2) (k₁ + 1) k₂ N → P x y (k₁ + 1) (k₂ + 1) (N + 1)) :
  P x y B₁ B₂ (B₁ + B₂) :=
begin
  suffices : ∀ n, n = B₁ + B₂ → ∃ (k₁ k₂ : ℕ), k₁ ≤ B₁ ∧ k₂ ≤ B₂ ∧ n = k₁ + k₂ ∧ P x y k₁ k₂ n,
  { obtain ⟨k₁, k₂, hk₁, hk₂, hn, he⟩ := this (B₁ + B₂) rfl,
    obtain ⟨rfl, rfl⟩ : k₁ = B₁ ∧ k₂ = B₂ := by split; linarith only [hk₁, hk₂, hn],
    exact he, },
  intros n hn,
  induction n with n ih generalizing B₁ B₂ x y,
  { use [0, 0], simpa using hP_base x y, },
  by_cases H : (a * b).valid (x, y), swap,
  { refine ⟨B₁, B₂, rfl.le, rfl.le, hn, hP_invalid _ _ _ _ _ H _ ha hb⟩, 
    simpa [not_and_distrib] using H, },
  cases B₁, { cases H.1.bound_pos ha, },
  cases B₂, { cases H.2.bound_pos hb, },
  simp [nat.succ_eq_add_one, ← add_assoc] at hn,
  by_cases h : a.to_order x ≤ b.to_order y,
  { -- Advance `a` (i.e. `a` ≤ `b`)
    rw [Stream.bound_valid_succ] at ha,
    obtain ⟨k₁, k₂, hk₁, hk₂, rfl, he⟩ := ih (ha H.1) hb (hn.trans (add_right_comm _ _ _)),
    refine ⟨k₁ + 1, k₂, nat.succ_le_succ hk₁, hk₂, (add_right_comm k₁ k₂ 1), _⟩,
    cases k₂, { exfalso, linarith only [hn, hk₁], },
    apply hP_advance_a _ _ _ _ _ H h he, },
  { -- Advance `b` (i.e. `b < a`)
    rw [Stream.bound_valid_succ] at hb,
    obtain ⟨k₁, k₂, hk₁, hk₂, rfl, he⟩ := ih ha (hb H.2) hn,
    refine ⟨k₁, k₂ + 1, hk₁, nat.succ_le_succ  hk₂, rfl, _⟩,
    cases k₁, { exfalso, linarith only [hn, hk₂], },
    apply hP_advance_b _ _ _ _ _ H (lt_of_not_le h) he, }
end

theorem Stream.mul_spec_value [non_unital_non_assoc_semiring α] {a : Stream ι α} {b : Stream ι α} (hsa : a.simple) (hsb : b.simple)
  {x y B₁ B₂} (ha : a.bound_valid B₁ x) (hb : b.bound_valid B₂ y) :
  (a * b).eval_steps (B₁ + B₂) (x, y) = (a.eval_steps B₁ x) * (b.eval_steps B₂ y) :=
begin
  apply Stream.mul_induction ha hb (λ x y k₁ k₂ N, (a * b).eval_steps N (x, y) = (a.eval_steps k₁ x) * (b.eval_steps k₂ y)); clear_except hsa hsb,
  { intros, simp, },
  { intros x y B₁ B₂ N H h ha hb,
    cases h; simp [Stream.eval_invalid h, Stream.eval_invalid H, Stream.next'_val_invalid' H], },
  { intros x y k₁ k₂ n H h he,
    simp [H, H.1, h, he, add_mul], congr,
    simp [H.2, mul_add, Stream.mul_eq_zero hsb H.1 H.2 h, Stream.mul_eval₀], },
  { intros x y k₁ k₂ n H h he,
    simp [H, H.2, h.not_le, he, mul_add], congr,
    simp [H.1, add_mul, Stream.mul_eval₀, Stream.mul_eq_zero' hsa H.1 H.2 h.le], },
end

theorem Stream.mul_spec_index [has_mul α] {a : Stream ι α} {b : Stream ι α}
  {x y B₁ B₂} (ha : a.bound_valid B₁ x) (hb : b.bound_valid B₂ y) :
  ((a * b).valid ((a * b).next'^[B₁ + B₂] (x, y)) → ((a * b).next'^[B₁ + B₂] (x, y)) = (a.next'^[B₁] x, b.next'^[B₂] y)) :=
begin
  apply Stream.mul_induction ha hb (λ x y k₁ k₂ N, (a * b).valid ((a * b).next'^[N] (x, y)) → ((a * b).next'^[N] (x, y)) = (a.next'^[k₁] x, b.next'^[k₂] y)); clear_except hsa hsb,
  { intros, simp, },
  { intros x y B₁ B₂ N H h ha hb, simp only [Stream.next'_val_invalid' H], exact false.elim ∘ H, },
  { intros x y k₁ k₂ n H h hiter,
    simp only [Stream.next'_val H, function.iterate_succ_apply, Stream.has_mul_mul_next, h, if_true, Stream.next'_val H.1],
    exact hiter, },
  { intros x y k₁ k₂ n H h hiter,
    simp only [Stream.next'_val H, function.iterate_succ_apply, Stream.has_mul_mul_next, h.not_le, if_false, Stream.next'_val H.2],
    exact hiter, },
end

@[simps]
instance {ι : Type} {α : Type*} [linear_order ι] [has_mul α] : has_mul (StreamExec ι α) := ⟨λ a b,
{ stream := a.stream * b.stream,
  state := (a.state, b.state),
  bound := a.bound + b.bound,
  bound_valid := begin
    rw [bound_valid_iff_next'_iterate],
    intro H,
    have := Stream.mul_spec_index a.bound_valid b.bound_valid H,
    dsimp at H, simp [this] at H,
    -- In fact, either `a` or `b` having a valid bound makes `a * b` have a valid bound
    -- We make an arbitrary choice here to use `a`
    refine absurd H.1 _,
    rw [← bound_valid_iff_next'_iterate],
    exact a.bound_valid,
  end }⟩

lemma StreamExec.mul_spec [non_unital_non_assoc_semiring α] (a : StreamExec ι α) (b : StreamExec ι α) (ha : a.stream.simple) (hb : b.stream.simple) :
  (a * b).eval = a.eval * b.eval := Stream.mul_spec_value ha hb a.bound_valid b.bound_valid

lemma Stream.mul_is_monotonic [has_mul α] {a : Stream ι α} {b : Stream ι α} (hsa : a.monotonic) (hsb : b.monotonic) :
  (a * b).monotonic :=
begin
  rintros ⟨x, y⟩ H,
  simp only [Stream.mul_index'],
  refine max_le_max _ _; simp; split_ifs,
  any_goals { exact rfl.le, },
  exacts [hsa _, hsb _],
end

lemma Stream.mul_is_simple [has_mul α] {a : Stream ι α} {b : Stream ι α} (hsa : a.simple) (hsb : b.simple) :
  (a * b).simple :=
begin
  refine ⟨Stream.mul_is_monotonic hsa.monotonic hsb.monotonic, _⟩,
  rintros ⟨x, y⟩ hv hr,
  simp only [Stream.mul_index', hr.index', max_self, Stream.has_mul_mul_next],
  split_ifs with H,
  { simp only [← hr.index', ne, max_ne_self_iff'], exact hsa.index_lt_next _ hr.r₁, },
  { simp only [hr.index', ne, max_ne_self_iff], exact hsb.index_lt_next _ hr.r₂, },
end

@[simps]
instance {ι : Type} {α : Type*} [linear_order ι] [has_mul α] : has_mul (SimpleStream ι α) := ⟨λ a b,
{ simple := Stream.mul_is_simple a.simple b.simple,
  ..(@has_mul.mul (StreamExec ι α) _ a b) }⟩

lemma SimpleStream.coe_mul {ι : Type} {α : Type*} [linear_order ι] [has_mul α] (a b : SimpleStream ι α) :
  (↑(a * b) : StreamExec ι α) = (↑a) * (↑b) := rfl

instance SimpleStream.MulEval [non_unital_non_assoc_semiring α] : MulEval (SimpleStream ι α) ι α :=
{ hmul := λ a b, StreamExec.mul_spec a b a.simple b.simple  }

section

lemma mul_value_eval {ι α ι' α' : Type*} [linear_order ι] [non_unital_non_assoc_semiring α'] [MulEval α ι' α'] 
  (a b : StreamExec ι α) :
  (Eval.eval <$₂> (a * b)) = (Eval.eval <$₂> a) * (Eval.eval <$₂> b) :=
begin
  ext; solve_refl,
  { simp only [Stream.mul.ready_iff], refl, },
  { simp, refl, },
end

-- huh??
instance {ι α ι' α' : Type*} [linear_order ι] [non_unital_non_assoc_semiring α'] [MulEval α ι' α'] :
  Eval (SimpleStream ι α) ι (ι' →₀ α') := SimpleStream.Eval_ind

instance {ι α ι' α' : Type*} [linear_order ι] [non_unital_non_assoc_semiring α'] [MulEval α ι' α'] :
  MulEval (SimpleStream ι α) ι (ι' →₀ α') :=
{ hmul := λ x y, by { simp [Eval.eval, mul_value_eval, SimpleStream.coe_mul], rw StreamExec.mul_spec, exacts [⟨x.monotonic, x.reduced⟩, ⟨y.monotonic, y.reduced⟩], } }

end
