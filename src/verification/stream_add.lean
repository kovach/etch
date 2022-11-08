import verification.stream_props
import verification.stream_zero
import verification.misc
import verification.finsuppeval
import tactic.zify
import tactic.linarith
import tactic.abel

open_locale classical
noncomputable theory

variables {ι : Type} {α : Type*}
  [linear_order ι]

section defs
variables [has_zero α]
  [has_add α]

@[simps]
instance : has_add (Stream ι α) := ⟨λ a b,
{ σ := a.σ × b.σ,
  valid := λ s, a.valid s.1 ∨ b.valid s.2,
  ready := λ s, (a.to_order s.1 ≤ b.to_order s.2 ∧ a.ready s.1) ∨ (b.to_order s.2 ≤ a.to_order s.1 ∧ b.ready s.2),
  next := λ s h, (if H : a.to_order s.1 ≤ b.to_order s.2 then a.next s.1 (valid_of_le_or h H) else s.1, 
                  if H : b.to_order s.2 ≤ a.to_order s.1 then b.next s.2 (valid_of_le_or h.symm H) else s.2),
  index := λ s h, option.get (show (min (a.index' s.1) (b.index' s.2)).is_some, by simpa),
  value := λ s h, (if a.to_order s.1 ≤ b.to_order s.2 then a.value' s.1 else 0) +
                  (if b.to_order s.2 ≤ a.to_order s.1 then b.value' s.2 else 0) }⟩ 

-- Some weird inequality lemma I extracted from the main proof
private lemma succ_le_min_succ_add_succ {a b b' d : ℕ} (ha : a ≤ b + d) (hb' : b ≤ b') :
  a + 1 ≤ (min b' (b + 1)) + (d + 1) :=
by { rw [← add_assoc, nat.succ_le_succ_iff, min_def], split_ifs; linarith, }

end defs

section lemmas
variables {a : Stream ι α} {b : Stream ι α} {x : a.σ} {y : b.σ}

section index_lemmas
variables [has_zero α] [has_add α]

lemma lt_index_of_valid (h : a.to_order x ≤ b.to_order y) (hva : a.valid x) :
  ↑(a.index x hva) ≤ b.index' y :=
by { simp only [← Stream.index'_val hva], exact prod.lex.fst_le_of_le h, }

lemma Stream.min_index (h : a.to_order x ≤ b.to_order y) (hva : a.valid x) :
  min (a.index' x) (b.index' y) = a.index x hva :=
by { rw [Stream.index'_val hva, min_eq_left_iff], exact lt_index_of_valid h hva, }

@[simp] lemma Stream.add_index' (a : Stream ι α) (b : Stream ι α) (xy : a.σ × b.σ) :
  (a + b).index' xy = min (a.index' xy.1) (b.index' xy.2) :=
begin
  rcases xy with ⟨x, y⟩,
  by_cases H : (a + b).valid (x, y),
  { simp [Stream.index'_val H], },
  { have : ¬a.valid x ∧ ¬b.valid y := by { simpa [not_or_distrib] using H, },
    simp [Stream.index', H, this], }
end

end index_lemmas

section value_lemmas
variables [add_comm_monoid α]

lemma Stream.add.eval₀_left (h : a.to_order x < b.to_order y) (hva H) :
  (a + b).eval₀ (x, y) H = a.eval₀ x hva :=
begin
  simp [Stream.eval₀, h.le, h.not_le],
  split_ifs with H,
  { simp [Stream.min_index h.le hva, Stream.value'_val H], },
  { refl, },
end

lemma Stream.add_eval₀_right (h : b.to_order y < a.to_order x) (hvb H) :
  (a + b).eval₀ (x, y) H = b.eval₀ y hvb :=
begin
  simp [Stream.eval₀, h.le, h.not_le],
  split_ifs with H,
  { simp [H, Stream.min_index h.le hvb, Stream.value'_val H, min_comm (a.index' _) _], },
  { refl, },
end

lemma Stream.add_eval₀_both (h : a.to_order x = b.to_order y) (hva hvb H) :
  (a + b).eval₀ (x, y) H = a.eval₀ x hva + b.eval₀ y hvb :=
begin
  simp [Stream.eval₀, h],
  have : a.index _ hva = b.index _ hvb, { simpa [Stream.index'_val hva, Stream.index'_val hvb] using congr_arg prod.fst h, },
  by_cases H₁ : a.ready x; by_cases H₂ : b.ready y; simp [H₁, H₂, Stream.value', Stream.min_index h.le hva, this],
end

end value_lemmas
end lemmas

@[elab_as_eliminator]
theorem Stream.add_induction [has_zero α] [has_add α] (a : Stream ι α) (b : Stream ι α) (x : a.σ) (y : b.σ)
  {B₁ B₂ : ℕ} (ha : a.bound_valid B₁ x) (hb : b.bound_valid B₂ y)
  (P : ∀ (x : a.σ) (y : b.σ) (k₁ : ℕ) (k₂ : ℕ) (N : ℕ), Prop)
  (hP_base : ∀ (x y), P x y 0 0 0)
  (hP_invalid : ∀ (x y B₁ B₂ N) (H : ¬(a + b).valid (x, y)) (hvx : ¬a.valid x) (hvy : ¬b.valid y), a.bound_valid B₁ x → b.bound_valid B₂ y → P x y B₁ B₂ N)
  (hP_advance_a : ∀ (x y k₁ k₂ N) (hvx : a.valid x), (a + b).valid (x, y) → a.to_order x < b.to_order y → P (a.next x hvx) y k₁ k₂ N → P x y (k₁ + 1) k₂ (N + 1))
  (hP_advance_b : ∀ (x y k₁ k₂ N) (hvy : b.valid y), (a + b).valid (x, y) → b.to_order y < a.to_order x → P x (b.next y hvy) k₁ k₂ N → P x y k₁ (k₂ + 1) (N + 1))
  (hP_advance_both : ∀ (x y k₁ k₂ B₁ N) (hvx : a.valid x) (hvy : b.valid y), (a + b).valid (x, y) → a.bound_valid (B₁ + 1) x → a.to_order x = b.to_order y → P (a.next x hvx) (b.next y hvy) k₁ k₂ N → P x y (min (B₁ + 1) (k₁ + 1)) (k₂ + 1) (N + 1)) :
  P x y B₁ B₂ (B₁ + B₂) :=
begin
  suffices : ∀ n ≤ B₁ + B₂, ∃ (k₁ k₂ : ℕ), k₁ ≤ B₁ ∧ k₂ ≤ B₂ ∧ n ≤ k₁ + k₂ ∧ P x y k₁ k₂ n,
  { obtain ⟨k₁, k₂, h₁, h₂, hn, hP⟩ := this (B₁ + B₂) rfl.le,
    obtain ⟨rfl, rfl⟩ : k₁ = B₁ ∧ k₂ = B₂ := by split; linarith only [h₁, h₂, hn],
    exact hP, },
  intros n hn,
  induction n with n ih generalizing B₁ B₂ x y,
  { use [0, 0], simpa using hP_base x y, },
  by_cases H : (a + b).valid (x, y), swap,
  { -- Invalid
    obtain ⟨hvx, hvy⟩ : ¬a.valid x ∧ ¬b.valid y := by simpa [not_or_distrib] using H,
    refine ⟨B₁, B₂, rfl.le, rfl.le, hn, _⟩, 
    exact hP_invalid _ _ _ _ _ H hvx hvy ha hb, },
  rcases lt_trichotomy (a.to_order x) (b.to_order y) with h|h|h, swap, rotate 1,
  { -- Advancing `a`
    have hvx : a.valid x := valid_of_le_or H h.le,
    cases B₁, { cases hvx.bound_pos ha, },
    rw [Stream.bound_valid_succ] at ha,
    obtain ⟨k₁, k₂, hk₁, hk₂, n_le, hP⟩ := ih (a.next _ hvx) y (ha hvx) hb (by simpa [nat.succ_eq_one_add, add_assoc] using hn),
    refine ⟨k₁ + 1, k₂, nat.succ_le_succ hk₁, hk₂, _, _⟩,
    { ac_change _ ≤ k₁ + k₂ + 1, exact nat.succ_le_succ n_le, },
    exact hP_advance_a _ _ _ _ _ hvx H h hP, },
  { -- Advancing `b`
    have hvy : b.valid y := valid_of_le_or (or.symm H) h.le,
    cases B₂, { cases hvy.bound_pos hb, },
    rw [Stream.bound_valid_succ] at hb,
    obtain ⟨k₁, k₂, hk₁, hk₂, n_le, hP⟩ := ih x (b.next _ hvy) ha (hb hvy) (nat.le_of_succ_le_succ hn),
    refine ⟨k₁, k₂ + 1, hk₁, nat.succ_le_succ hk₂, nat.succ_le_succ n_le, _⟩,
    exact hP_advance_b _ _ _ _ _ hvy H h hP, },
  { -- Advancing both `a` and `b`
    have hvx : a.valid x := valid_of_le_or H h.le,
    have hvy : b.valid y := valid_of_le_or (or.symm H) h.symm.le,
    cases B₁, { cases hvx.bound_pos ha, },
    cases B₂, { cases hvy.bound_pos hb, },
    have ha' := ha, rw nat.succ_eq_add_one at ha',
    rw [Stream.bound_valid_succ] at ha hb,
    obtain ⟨k₁, k₂, hk₁, hk₂, n_le, hP⟩ := ih (a.next _ hvx) (b.next _ hvy) ((ha hvx).mono B₁.le_succ) (hb hvy) (nat.le_of_succ_le_succ hn),
    refine ⟨min (B₁ + 1) (k₁ + 1), k₂ + 1, min_le_left _ _, nat.succ_le_succ hk₂, succ_le_min_succ_add_succ n_le hk₁, _⟩, 
    exact hP_advance_both _ _ _ _ _ _ hvx hvy H ha' h hP, }
end

theorem Stream.add_spec [add_comm_monoid α] (a : Stream ι α) (b : Stream ι α) (x : a.σ) (y : b.σ)
  {B₁ B₂ : ℕ} (ha : a.bound_valid B₁ x) (hb : b.bound_valid B₂ y) :
  (a + b).eval_steps (B₁ + B₂) (x, y) = a.eval_steps B₁ x + b.eval_steps B₂ y :=
begin
  apply Stream.add_induction a b x y ha hb (λ x y k₁ k₂ N, (a + b).eval_steps N (x, y) = a.eval_steps k₁ x + b.eval_steps k₂ y); clear_except,
  { intros, simp, },
  { intros x y B₁ B₂ n H hvx hvy ha hb,
    simp [Stream.eval_invalid H, Stream.eval_invalid hvx, Stream.eval_invalid hvy], },
  { intros x y k₁ k₂ n hvx H h he,
    dsimp, simp [h.le, h.not_le, he, Stream.add.eval₀_left h hvx, H, hvx],
    apply add_right_comm, },
  { intros x y k₁ k₂ n hvy H h he, 
    dsimp [nat.add_succ], simp [H, hvy, h.le, h.not_le, he, Stream.add_eval₀_right h hvy, add_assoc], },
  { intros x y k₁ k₂ B₁ n hvx hvy H ha h he, 
    rw Stream.eval_min_bound ha,
    dsimp, simp [h.le, h.symm.le, he, Stream.add_eval₀_both h hvx hvy, H, hvx, hvy],
    abel, },
end

theorem Stream.add_spec_index [has_zero α] [has_add α] (a : Stream ι α) (b : Stream ι α) (x : a.σ) (y : b.σ)
  {B₁ B₂ : ℕ} (ha : a.bound_valid B₁ x) (hb : b.bound_valid B₂ y) :
  ((a + b).next'^[B₁ + B₂] (x, y)) = (a.next'^[B₁] x, b.next'^[B₂] y) :=
begin
  apply Stream.add_induction a b x y ha hb (λ x y k₁ k₂ N, ((a + b).next'^[N] (x, y)) = (a.next'^[k₁] x, b.next'^[k₂] y)); clear_except,
  { intros, simp, },
  { intros x y B₁ B₂ n H hvx hvy ha hb, 
    simp [Stream.next'_val_invalid' H, Stream.next'_val_invalid' hvx, Stream.next'_val_invalid' hvy], },
  { intros x y k₁ k₂ n hvx H h hiter,
    simp [Stream.next'_val hvx, Stream.next'_val H, h.le, h.not_le, hiter], },
  { intros x y k₁ k₂ n hvy H h hiter,
    simp [Stream.next'_val hvy, Stream.next'_val H, h.le, h.not_le, hiter], },
  { intros x y k₁ k₂ B₁ n hvx hvy H ha h hiter, 
    rw Stream.next'_min_bound ha,
    simp [h.le, h.symm.le, hiter, Stream.next'_val hvx, Stream.next'_val hvy, Stream.next'_val H], }
end

@[simps]
instance [has_zero α] [has_add α] : has_add (StreamExec ι α) := ⟨λ a b,
{ stream := a.stream + b.stream,
  state := (a.state, b.state),
  bound := a.bound + b.bound,
  bound_valid := begin
    rw [bound_valid_iff_next'_iterate], dsimp,
    simpa [bound_valid_iff_next'_iterate, (Stream.add_spec_index a.stream b.stream _ _ a.bound_valid b.bound_valid),
      not_or_distrib] using (and.intro a.bound_valid b.bound_valid),
  end }⟩

@[simp] lemma StreamExec.add_spec [add_comm_monoid α] (a : StreamExec ι α) (b : StreamExec ι α) :
  (a + b).eval = a.eval + b.eval := (Stream.add_spec a.stream b.stream _ _ a.bound_valid b.bound_valid)

lemma Stream.add_monotonic [has_zero α] [has_add α] {a : Stream ι α} {b : Stream ι α}
  (ha : a.monotonic) (hb : b.monotonic) :
  (a + b).monotonic :=
begin
  rintros ⟨x, y⟩ h,
  simp only [Stream.add_index'],
  refine min_le_min _ _,
  { simp, split_ifs, { exact ha _, }, exact rfl.le, },
  { simp, split_ifs, { exact hb _, }, exact rfl.le, },
end

lemma Stream.add_reduced [has_zero α] [has_add α] {a : Stream ι α} {b : Stream ι α}
  (ha : a.reduced) (hb : b.reduced) : (a + b).reduced :=
begin
  rintros ⟨x, y⟩ hv hr,
  rcases hr with ⟨h, hr⟩|⟨h, hr⟩;
  dsimp at hr h ⊢,
  { simp [h, (show min (a.index' x) (b.index' y) = _, from min_eq_left (prod.lex.fst_le_of_le h))],
    apply ne_min_of_ne_and_ne, { exact ha _ hr, },
    split_ifs with H,
    { obtain ⟨h₁, h₂⟩ : a.index' x = b.index' y ∧ (a.ready x ↔ b.ready y),
      { simpa [Stream.to_order] using (antisymm h H), },
      rw h₁, exact hb _ (by rwa ← h₂), },
    exact ne_of_lt (prod.lex.fst_lt_of_lt_of_le (lt_of_le_not_le h H) (by simp [hr])), },
  { simp [h, (show min (a.index' x) (b.index' y) = _, from min_eq_right (prod.lex.fst_le_of_le h))],
    apply ne_min_of_ne_and_ne, swap, { exact hb _ hr, },
    split_ifs with H,
    { obtain ⟨h₁, h₂⟩ : a.index' x = b.index' y ∧ (a.ready x ↔ b.ready y),
      { simpa [Stream.to_order] using (antisymm H h), },
      rw ← h₁, exact ha _ (by rwa h₂), },
    exact ne_of_lt (prod.lex.fst_lt_of_lt_of_le (lt_of_le_not_le h H) (by simp [hr])), },
end

lemma Stream.add_simple [has_zero α] [has_add α] {a : Stream ι α} {b : Stream ι α} (ha : a.simple) (hb : b.simple) :
  (a + b).simple :=
{ monotonic := Stream.add_monotonic ha.monotonic hb.monotonic,
  reduced := Stream.add_reduced ha.reduced hb.reduced, }

instance StreamExec.AddZeroEval [add_comm_monoid α] : AddZeroEval (StreamExec ι α) ι α :=
{ hadd := StreamExec.add_spec,
  hzero := StreamExec.zero_eval }

lemma add_value_eval {ι α ι' α' : Type*} [linear_order ι] [add_comm_monoid α'] [AddZeroEval α ι' α'] 
  (a b : StreamExec ι α) :
  (Eval.eval <$₂> (a + b)) = (Eval.eval <$₂> a) + (Eval.eval <$₂> b) :=
begin
  ext; solve_refl,
  simp [apply_ite Eval.eval],
  congr; rw [Stream.bimap_value'_apply]; simp,
end

instance {ι α ι' α' : Type*} [linear_order ι] [add_comm_monoid α'] [AddZeroEval α ι' α'] :
  AddZeroEval (StreamExec ι α) ι (ι' →₀ α') :=
{ hadd := λ x y, by simp [Eval.eval, add_value_eval],
  hzero := StreamExec.zero_eval }

example {ι₁ ι₂ : Type} [linear_order ι₁] [linear_order ι₂]
  (a b : StreamExec ι₁ (StreamExec ι₂ ℤ)) :
  Eval.eval (a + b) = (Eval.eval a) + (Eval.eval b) := by simp
