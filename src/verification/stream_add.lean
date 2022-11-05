import verification.stream_props
import verification.misc
import tactic.zify
import tactic.linarith
import tactic.abel

open_locale classical
noncomputable theory

variables {σ σ₁ σ₂ ι α : Type}
  [linear_order ι]
  [non_unital_semiring α]

@[simps]
def Stream.add (a : Stream σ₁ ι α) (b : Stream σ₂ ι α) : Stream (σ₁ × σ₂) ι α :=
{ valid := λ s, a.valid s.1 ∨ b.valid s.2,
  ready := λ s, a.ready s.1 ∨ b.ready s.2,
  next := λ s h, (if H : a.to_order s.1 ≤ b.to_order s.2 then a.next s.1 (valid_of_le_or h H) else s.1, 
                  if H : b.to_order s.2 ≤ a.to_order s.1 then b.next s.2 (valid_of_le_or h.symm H) else s.2),
  index := λ s h, option.get (show (min (a.index' s.1) (b.index' s.2)).is_some, by simpa),
  value := λ s h, (if a.to_order s.1 ≤ b.to_order s.2 then a.value' s.1 else 0) +
                  (if b.to_order s.2 ≤ a.to_order s.1 then b.value' s.2 else 0) }

infixl ` +ₛ `:80 := Stream.add

def StreamExec.add (a : StreamExec σ₁ ι α) (b : StreamExec σ₂ ι α) : StreamExec (σ₁ × σ₂) ι α :=
{ stream := a.stream +ₛ b.stream,
  state := (a.state, b.state),
  bound := a.bound + b.bound } 

infixl ` +ₑ `:80 := StreamExec.add

-- Some weird inequality lemma I extracted from the main proof
private lemma succ_le_min_succ_add_succ {a b b' d : ℕ} (ha : a ≤ b + d) (hb' : b ≤ b') :
  a + 1 ≤ (min b' (b + 1)) + (d + 1) :=
by { rw [← add_assoc, nat.succ_le_succ_iff, min_def], split_ifs; zify at *; linarith, }

section lemmas
variables {a : Stream σ₁ ι α} {b : Stream σ₂ ι α} {x : σ₁} {y : σ₂}

lemma lt_index_of_valid (h : a.to_order x ≤ b.to_order y) (hva : a.valid x) :
  ↑(a.index x hva) ≤ b.index' y :=
by { simp only [← Stream.index'_val hva], exact prod.lex.fst_le_of_le h, }

lemma Stream.min_index (h : a.to_order x ≤ b.to_order y) (hva : a.valid x) :
  min (a.index' x) (b.index' y) = a.index x hva :=
by { rw [Stream.index'_val hva, min_eq_left_iff], exact lt_index_of_valid h hva, }

lemma Stream.add.eval₀_left (h : a.to_order x < b.to_order y) (hva H) :
  (a +ₛ b).eval₀ (x, y) H = a.eval₀ x hva :=
begin
  simp [Stream.eval₀, h.le, h.not_le],
  by_cases H : a.ready x,
  { simp [H, Stream.min_index h.le hva, Stream.value'_val H], },
  { simp [H, Stream.value'], },
end

lemma Stream.add_eval₀_right (h : b.to_order y < a.to_order x) (hvb H) :
  (a +ₛ b).eval₀ (x, y) H = b.eval₀ y hvb :=
begin
  simp [Stream.eval₀, h.le, h.not_le],
  by_cases H : b.ready y,
  { simp [H, Stream.min_index h.le hvb, Stream.value'_val H, min_comm (a.index' _) _], },
  { simp [H, Stream.value'], },
end

lemma Stream.add_eval₀_both (h : a.to_order x = b.to_order y) (hva hvb H) :
  (a +ₛ b).eval₀ (x, y) H = a.eval₀ x hva + b.eval₀ y hvb :=
begin
  simp [Stream.eval₀, h],
  have : a.index _ hva = b.index _ hvb, { simpa [Stream.to_order, Stream.index'_val hva, Stream.index'_val hvb] using congr_arg prod.fst h, },
  by_cases H₁ : a.ready x; by_cases H₂ : b.ready y; simp [H₁, H₂, Stream.value', Stream.min_index h.le hva, this],
end

end lemmas

theorem Stream.add_spec (a : Stream σ₁ ι α) (b : Stream σ₂ ι α) (x : σ₁) (y : σ₂) (n : ℕ)
  {B₁ B₂ : ℕ} (ha : a.bound_valid B₁ x) (hb : b.bound_valid B₂ y) (hn : n ≤ B₁ + B₂) :
  ∃ (k₁ k₂ : ℕ), k₁ ≤ B₁ ∧ k₂ ≤ B₂ ∧ n ≤ k₁ + k₂ ∧ (a +ₛ b).eval_steps n (x, y) = a.eval_steps k₁ x + b.eval_steps k₂ y :=
begin
  induction n with n ih generalizing B₁ B₂ x y,
  { use [0, 0], simp, },
  by_cases H : (a +ₛ b).valid (x, y), swap,
  { -- Invalid
    refine ⟨B₁, B₂, rfl.le, rfl.le, hn, _⟩,
    obtain ⟨hvx, hvy⟩ : ¬a.valid x ∧ ¬b.valid y := by simpa [not_or_distrib] using H,
    simp [Stream.eval_invalid H, Stream.eval_invalid hvx, Stream.eval_invalid hvy], },
  rcases lt_trichotomy (a.to_order x) (b.to_order y) with _|_|_, swap, rotate 1,
  { -- Advancing `a`
    have hvx : a.valid x := valid_of_le_or H h.le,
    cases B₁, { cases hvx.bound_pos ha, },
    rw [Stream.bound_valid_succ] at ha,
    obtain ⟨k₁, k₂, hk₁, hk₂, n_le, he⟩ := ih (a.next _ hvx) y (ha hvx) hb (by simpa [nat.succ_eq_one_add, add_assoc] using hn),
    refine ⟨k₁ + 1, k₂, nat.succ_le_succ hk₁, hk₂, _, _⟩,
    { ac_change _ ≤ k₁ + k₂ + 1, exact nat.succ_le_succ n_le, },
    simp [H, hvx], dsimp, simp [h.le, h.not_le, he, Stream.add.eval₀_left h hvx],
    exact add_right_comm _ _ _, },
  { -- Advancing `b`
    have hvy : b.valid y := valid_of_le_or (or.symm H) h.le,
    cases B₂, { cases hvy.bound_pos hb, },
    rw [Stream.bound_valid_succ] at hb,
    obtain ⟨k₁, k₂, hk₁, hk₂, n_le, he⟩ := ih x (b.next _ hvy) ha (hb hvy) (nat.le_of_succ_le_succ hn),
    refine ⟨k₁, k₂ + 1, hk₁, nat.succ_le_succ hk₂, nat.succ_le_succ n_le, _⟩,
    simp [H, hvy], dsimp, simp [h.le, h.not_le, he, Stream.add_eval₀_right h hvy, add_assoc], },
  { -- Advancing both `a` and `b`
    have hvx : a.valid x := valid_of_le_or H h.le,
    have hvy : b.valid y := valid_of_le_or (or.symm H) h.symm.le,
    cases B₁, { cases hvx.bound_pos ha, },
    cases B₂, { cases hvy.bound_pos hb, },
    have ha' := ha, rw nat.succ_eq_add_one at ha',
    rw [Stream.bound_valid_succ] at ha hb,
    obtain ⟨k₁, k₂, hk₁, hk₂, n_le, he⟩ := ih (a.next _ hvx) (b.next _ hvy) ((ha hvx).mono B₁.le_succ) (hb hvy) (nat.le_of_succ_le_succ hn),
    refine ⟨min (B₁ + 1) (k₁ + 1), k₂ + 1, min_le_left _ _, nat.succ_le_succ hk₂, succ_le_min_succ_add_succ n_le hk₁, _⟩,
    rw Stream.eval_min_bound ha',
    simp [H, hvx, hvy], dsimp, simp [h.le, h.symm.le, he, Stream.add_eval₀_both h hvx hvy],
    abel, }
end 

lemma StreamExec.add_spec (a : StreamExec σ₁ ι α) (b : StreamExec σ₂ ι α) (ha : a.bound_valid) (hb : b.bound_valid) :
  (a +ₑ b).eval = a.eval + b.eval :=
begin
  simp only [StreamExec.eval],
  obtain ⟨k₁, k₂, hk₁, hk₂, H, he⟩ := Stream.add_spec a.stream b.stream _ _ (a.bound + b.bound) ha hb rfl.le,
  obtain ⟨rfl, rfl⟩ : k₁ = a.bound ∧ k₂ = b.bound, { split; zify at H hk₁ hk₂ ⊢; linarith only [hk₁, hk₂, H], }, 
  exact he,
end

/-
lemma : ∀ n, ∃ (k₁ ≤ a.bound, k₂ ≤ b.bound), s.t. n ≤ k₁ + k₂ ∧ (a + b).eval_steps n = (a.eval_steps k₁ + b.eval_steps k₂)

WLOG k₁, k₂ ≤ bound

∀ n, ∃ (k₁ ≤ a.bound, k₂ ≤ b.bound), s.t. n ≤ k₁ + k₂ ∧ (a + b).eval_steps n = (a.eval_steps k₁ + b.eval_steps k₂)
n = (a + b).bound = a.bound + b.bound
-/

