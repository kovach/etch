import algebra
import algebra.group
import algebra.group.defs
import tactic
import logic.relation
import base
import monotonic
import data.stream.basic

namespace iter

universes u v
variables {α β : Type*}

section params_unary
variables {σ I V : Type} [linear_order I]
[decidable_eq σ]
(a : iter σ I V)
variables (s t : σ)

section semantics
variable [add_comm_monoid V]

end semantics

lemma step_progress_min {a : iter σ I V} {s} {i : ℕ} : a.minimal_terminal s i.succ → a.minimal_terminal (a.δ s) i := begin
simp only [minimal_terminal], rw step_succ, rintros ⟨t, h⟩, split, assumption,
intros j t2, rw step_succ at t2, exact nat.le_of_succ_le_succ (h _ t2),
end

lemma step_progress {a : iter σ I V} {s} {i : ℕ}
: a.terminal_by s i.succ → a.terminal_by (a.δ s) i := begin
simp only [terminal_by],
rw step_succ,
exact id,
end
-- mpr of step_progress, not used
-- lemma terminal_of_terminal {a : iter σ I V} {s} {i : ℕ}
-- : a.terminal_by (a.δ s) i → a.terminal_by s i.succ := begin
-- simp only [terminal_by],
-- rw step_succ,
-- exact id,
-- end

lemma terminal_mono {a : iter σ I V} {s} (i i' : ℕ) :
a.monotonic → a.terminal_by s i → i ≤ i' → a.terminal_by s i' := begin
intros mono fin hle,
obtain ⟨k,_⟩ := le_iff_exists_add.mp hle,
induction k with n hn generalizing s i i'; rw h, exact fin,
--change a.terminal_by s (i + n).succ,
apply terminal_succ_terminal _ mono,
exact hn _ _ fin (le_iff_exists_add.mpr ⟨n, rfl⟩) rfl,
end

end params_unary

section params_binary

variables {σ₁ σ₂ I V : Type} [linear_order I] [decidable_eq σ₁] [decidable_eq σ₂] [add_comm_monoid V]
(a : iter σ₁ I V) (b : iter σ₂ I V)

-- lemma step_trichotomy (s₁:σ₁)(s₂:σ₂) : ((a +'b).δ (s₁,s₂)) = (a.δ s₁, s₂) ∨ ((a +'b).δ (s₁,s₂)) = (a.δ s₁, b.δ s₂) ∨ ((a +'b).δ (s₁,s₂)) = (s₁, b.δ s₂) := begin
-- simp only [add_iter, iter.δ], split_ifs, tidy,
-- end

lemma step_trichotomy (s₁:σ₁)(s₂:σ₂)
:  (((a +'b).δ (s₁,s₂)) = (a.δ s₁, s₂) ∧ ¬ a.terminal s₁)
∨ (((a +'b).δ (s₁,s₂)) = (a.δ s₁, b.δ s₂) ∧ (a.terminal s₁ ∧ b.terminal s₂ ∨ ¬a.terminal s₁ ∧ ¬b.terminal s₂))
∨ (((a +'b).δ (s₁,s₂)) = (s₁, b.δ s₂) ∧ ¬ b.terminal s₂) := begin
simp only [add_iter, iter.δ], split_ifs, tidy,
{
  apply or.inl,
  intro h1,
  have : _ := emit_none_of_terminal h1,
  have : _ := ι_top_emit_none.mpr this,
  rw h_h_w at this,
  exact option.some_ne_none _ this,
},
{
  apply or.inr,
  apply or.inr,
  intro h1,
  have : _ := emit_none_of_terminal h1,
  have : _ := ι_top_emit_none.mpr this,
  rw h_1_h_w at this,
  exact option.some_ne_none _ this,
},
{
  apply or.inr, apply or.inl,
  have : a.ι s₁ = b.ι s₂ := le_antisymm h_1 h,
  cases h2 : a.ι s₁; rw h2 at this,
  {apply or.inl, exact ⟨h2, this.symm⟩},
  {apply or.inr, exact ⟨some_not_terminal h2, some_not_terminal this.symm⟩},
},
end

lemma sum_zero {i j : ℕ} : 0 = i + j → i = 0 ∧ j = 0 := begin
induction i; induction j, tidy,
end

lemma add_iter_bound {a : iter σ₁ I V} {b : iter σ₂ I V} {s₁ : σ₁} {s₂ : σ₂} {i j : ℕ}
  : a.monotonic → b.monotonic → a.terminal_by s₁ i → b.terminal_by s₂ j → (a+'b).terminal_by (s₁,s₂) (i+j) := λ amono bmono,
begin
obtain ⟨n, hnij⟩ : ∃ n, n = i + j := ⟨_, rfl⟩,
induction n with n hn generalizing i j s₁ s₂,
obtain ⟨i0, j0⟩ := sum_zero hnij, simp [i0, j0, minimal_terminal, step, one_smul],
intros h1 h2, simp [terminal_by, ι, emit, add_emit, h1, h2, le_top],
apply add_iter_terminal h1 h2,
intros h1 h2,
obtain (h|⟨heq, hterm⟩|h) := step_trichotomy a b s₁ s₂,
{ -- a.δ
  simp only [terminal_by],
  rw [← hnij, ← step_succ, h.1],
  change (a+'b).terminal_by (a.δ s₁, s₂) n,
  obtain ⟨i', h3⟩ := not_terminal_succ h.2 h1,
  rw h3 at h1,
  have h4 := step_progress h1,
  have : n = i' + j := _,
  { rw this,
    exact hn this h4 h2,
  },
  rw h3 at hnij, rw nat.succ_add at hnij,
  exact nat.succ.inj hnij,
},
swap,
{ -- b.δ
  simp only [terminal_by],
  rw [← hnij, ← step_succ, h.1],
  change (a+'b).terminal_by (s₁, b.δ s₂) n,
  obtain ⟨j', h3⟩ := not_terminal_succ h.2 h2,
  rw h3 at h2,
  have h4 := step_progress h2,
  have : n = i + j' := _,
  rw this,
  exact hn this h1 h4,
  rw h3 at hnij, rw nat.add_succ at hnij,
  exact nat.succ.inj hnij,
},
{ -- a.δ, b.δ
cases hterm,
  { -- the only place we use monotonicity (i+j might go too far)
    apply terminal_mono 0 (i+j) (add_iter_monotonic amono bmono)
        (add_iter_terminal hterm.1 hterm.2) (nat.zero_le _),
  },
  {
    simp only [terminal_by],
    rw [← hnij, ← step_succ, heq],
    change (a+'b).terminal_by (a.δ s₁, b.δ s₂) n,
    obtain ⟨i', hi'⟩ := not_terminal_succ hterm.1 h1,
    obtain ⟨j', hj'⟩ := not_terminal_succ hterm.2 h2,
    rw hi' at h1,
    rw hj' at h2,
    have h3 := step_progress h1,
    have h4 := step_progress h2,
    have h4' := terminal_mono j' j'.succ bmono h4 (nat.le_succ _),
    rw ← hj' at h4',
    have : n = i' + j := _,
    rw this,
    exact hn this h3 h4',
    { rw hj',
      rw [hi', hj'] at hnij,
      have : n = i'.succ + j' := nat.succ.inj hnij,
      rw nat.succ_add at this,
      exact this,
    }
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
