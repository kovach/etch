-- main theorem: add_iter_finite
import algebra
import combinators
import add_monotonic

namespace iter

universes u v
variables {α β : Type*}

section params_unary
variables {σ I V : Type} [linear_order I]
[has_zero V] [has_add V]
{a : iter σ I V}
variables (s t : σ)

@[simp] lemma step_progress_iff {s} {i : ℕ} : a.terminal_by s i.succ ↔ a.terminal_by (a.δ s) i := by simp
lemma step_progress {s} {i : ℕ} : a.terminal_by s i.succ → a.terminal_by (a.δ s) i := step_progress_iff.mp

lemma terminal_by_mono {s} (i i' : ℕ) :
a.monotonic → a.terminal_by s i → i ≤ i' → a.terminal_by s i' := begin
intros mono fin hle,
obtain ⟨k,_⟩ := le_iff_exists_add.mp hle,
induction k with n hn generalizing s i i'; rw h, exact fin,
apply terminal_succ_terminal _ mono,
exact hn _ _ fin (le_iff_exists_add.mpr ⟨n, rfl⟩) rfl,
end

end params_unary

section params_binary

variables {σ₁ σ₂ I V : Type} [linear_order I] [add_monoid V]
{a : iter σ₁ I V} {b : iter σ₂ I V}
{s₁ : σ₁} {s₂ : σ₂}

-- lemma step_trichotomy (s₁:σ₁)(s₂:σ₂) : ((a +'b).δ (s₁,s₂)) = (a.δ s₁, s₂) ∨ ((a +'b).δ (s₁,s₂)) = (a.δ s₁, b.δ s₂) ∨ ((a +'b).δ (s₁,s₂)) = (s₁, b.δ s₂) := begin
-- simp only [add_iter, iter.δ], split_ifs, tidy,
-- end

lemma step_sem_trichotomy (a : iter σ₁ I V) (b : iter σ₂ I V) (s₁:σ₁) (s₂:σ₂)
:  (((a +'b).δ (s₁,s₂)) = (a.δ s₁, s₂) ∧ ¬ a.terminal s₁ ∧ (a+'b).semantics₁ (s₁, s₂) = a.semantics₁ s₁)
∨ (((a +'b).δ (s₁,s₂)) = (a.δ s₁, b.δ s₂) ∧ (a.terminal s₁ ∧ b.terminal s₂ ∨ ¬a.terminal s₁ ∧ ¬b.terminal s₂) ∧ (a+'b).semantics₁ (s₁, s₂) = a.semantics₁ s₁ + b.semantics₁ s₂)
∨ (((a +'b).δ (s₁,s₂)) = (s₁, b.δ s₂) ∧ ¬ b.terminal s₂ ∧ (a+'b).semantics₁ (s₁, s₂) = b.semantics₁ s₂) :=
begin
simp only [semantics₁, add_emit, add_iter, iter.δ],
split_ifs with h1 h2 h3 h4,
{
  rcases h1 with ⟨_,⟨hi1,_⟩⟩,
  simp only [and_true, true_and, eq_self_iff_true, option.mem_def] at *,
  apply or.inl,
  intro h1,
  replace := emit_none_of_terminal h1,
  replace := ι_top_emit_none.mpr this,
  rw hi1 at this,
  exact option.some_ne_none _ this,
},
{
  rcases h2 with ⟨_,⟨hi2,_⟩⟩,
  simp only [true_and, and_true, not_lt, eq_self_iff_true, option.mem_def] at *,
  apply or.inr,
  apply or.inr,
  intro h1,
  have := emit_none_of_terminal h1,
  have := ι_top_emit_none.mpr this,
  rw hi2 at this,
  exact option.some_ne_none _ this,
},
{
  simp only [true_and, and_true, not_lt, prod.mk.inj_iff, eq_self_iff_true] at *,
  apply or.inr, apply or.inl,
  have : a.ι s₁ = b.ι s₂ := le_antisymm h2 h1,
  split,
  cases h2 : a.ι s₁; rw h2 at this,
  {apply or.inl, exact ⟨h2, this.symm⟩},
  {apply or.inr, exact ⟨some_not_terminal h2, some_not_terminal this.symm⟩},
  cases h3 : a.emit s₁ with v1;
  cases h4 : b.emit s₂ with v2,
  case option.some option.some {
    cases v1 with i1 v1; cases v2 with i2 v2,
    have : i1 = i2,
    { simp only [ι, h3, h4] at this,
      apply option.some.inj this },

    cases v1; cases v2;
    simp only [option.lift_or_get, merge_indexed_values, semantics₁, add_zero, zero_add, this],
    simp only [elementary], funext j, split_ifs with h; {simp [h, this]},
  },
  all_goals { simp  },
},
end

lemma step_trichotomy (a : iter σ₁ I V) (b : iter σ₂ I V) (s₁:σ₁) (s₂:σ₂)
:  (((a +'b).δ (s₁,s₂)) = (a.δ s₁, s₂) ∧ ¬ a.terminal s₁)
∨ (((a +'b).δ (s₁,s₂)) = (a.δ s₁, b.δ s₂) ∧ (a.terminal s₁ ∧ b.terminal s₂ ∨ ¬a.terminal s₁ ∧ ¬b.terminal s₂))
∨ (((a +'b).δ (s₁,s₂)) = (s₁, b.δ s₂) ∧ ¬ b.terminal s₂) := begin
obtain (h|h|h) := step_sem_trichotomy a b s₁ s₂,
exact or.inl ⟨h.1, h.2.1⟩,
exact or.inr (or.inl ⟨h.1, h.2.1⟩),
exact or.inr (or.inr ⟨h.1, h.2.1⟩),
end

@[simp] lemma sum_zero {i j : ℕ} : 0 = i + j ↔ i = 0 ∧ j = 0 := begin
induction i; induction j; dec_trivial,
end

lemma add_iter_bound {s₁ : σ₁} {s₂ : σ₂} {i j : ℕ}
  : a.monotonic → b.monotonic → a.terminal_by s₁ i → b.terminal_by s₂ j → (a+'b).terminal_by (s₁,s₂) (i+j) := λ amono bmono,
begin
--obtain ⟨n, hnij⟩ : ∃ n, n = i + j := ⟨_, rfl⟩,
generalize hnij : i+j = n,
induction n with n hn generalizing i j s₁ s₂,
{ obtain ⟨i0, j0⟩ := sum_zero.1 hnij.symm,
  intros h1 h2, --simp [terminal_by, ι, emit, add_emit, h1, h2, le_top],
  simp [*, step, one_smul, add_iter_terminal] at * },
intros h1 h2,
obtain (h|⟨heq, hterm⟩|h) := step_trichotomy a b s₁ s₂,
{ -- a.δ
  rw [terminal_by, step_succ, h.1, ←terminal_by],
  obtain ⟨i', h3⟩ := not_terminal_succ h.2 h1,
  rw h3 at h1,
  refine hn _ (step_progress h1) h2,
  { simp only [*, nat.succ_add] at * },
},
swap,
{ -- b.δ
  rw [terminal_by, step_succ, h.1, ←terminal_by],
  obtain ⟨j', h3⟩ := not_terminal_succ h.2 h2,
  rw h3 at h2,
  refine hn _ h1 (step_progress h2),
  { simp only [*, nat.add_succ] at * }
},
{ -- a.δ, b.δ
cases hterm,
  { -- the only place we use monotonicity (i+j might go too far)
    apply terminal_by_mono 0 _ (add_iter_monotonic amono bmono)
        (add_iter_terminal hterm.1 hterm.2) (nat.zero_le _),
  },
  {
    rw [terminal_by, step_succ, heq, ← terminal_by],
    obtain ⟨i', hi'⟩ := not_terminal_succ hterm.1 h1,
    obtain ⟨j', hj'⟩ := not_terminal_succ hterm.2 h2,
    rw hi' at h1,
    rw hj' at h2,
    have h3 := step_progress h1,
    have h4 := step_progress h2,
    replace h4 := terminal_by_mono j' j'.succ bmono h4 (nat.le_succ _),
    rw ← hj' at h4,
    refine hn (by simp only [*, nat.succ_add] at *) h3 h4,
  },
},
end

theorem add_iter_finite {a : iter σ₁ I V} {b : iter σ₂ I V} {s₁:σ₁} {s₂:σ₂}
: a.monotonic → b.monotonic → a.finite s₁ → b.finite s₂ → (a +' b).finite (s₁,s₂) := begin
rintros amono bmono ⟨ta, fina⟩ ⟨tb, finb⟩,
obtain ⟨i,hi⟩ := index_of_path fina.1,
obtain ⟨j,hj⟩ := index_of_path finb.1,
rw hi at fina,
rw hj at finb,
have reachable := path_of_index (s₁,s₂) (i+j),
have terminal := add_iter_bound amono bmono (fina.2) (finb.2),
exact ⟨_, ⟨reachable, terminal⟩⟩,
end

end params_binary

end iter
