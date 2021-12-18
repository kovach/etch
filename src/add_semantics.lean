-- main theorem: add_iter_sound
import algebra
import base
import tactics
import add_monotonic
import add_finite

namespace iter

section params_unary
variables {σ I V : Type} [linear_order I]
[decidable_eq σ]
{a : iter σ I V}
variables (s t : σ)

section semantics
variable [add_comm_monoid V]

@[simp] theorem terminal_zero {a : iter σ I V} (h : a.terminal t) : a.semantics₁ t = 0 := by simp *

@[simp]
theorem semantics_zero {t} {a : iter σ I V} (m : a.monotonic) (h : a.terminal t) (j:ℕ) : a.semantics' t j = 0 := begin
induction j with _ jh generalizing t,
all_goals {simp *}
end

lemma succ_of_ge_succ {i i' : ℕ} : i.succ ≤ i' → ∃ i'':ℕ, i' = i''.succ := λ h, begin
cases i',
{ exact false.rec _ (nat.not_succ_le_zero _ h) },
{ exact ⟨i', rfl⟩ },
end

theorem semantics_mono {i i'} {s} : a.monotonic → a.terminal_by s i → i ≤ i' → a.semantics' s i = a.semantics' s i' := λ mono fin hle, begin
induction i with i hi generalizing i' s,
{ simp * at * },
obtain ⟨i'', h1⟩ := succ_of_ge_succ hle,
rw h1 at *,
simp only [semantics'],
replace : i ≤ i'' := nat.le_of_succ_le_succ hle,
rw hi (step_progress fin) this,
end

end semantics
end params_unary

section params_binary

variables {σ₁ σ₂ I V : Type} [linear_order I] [decidable_eq σ₁] [decidable_eq σ₂] [add_comm_monoid V]
{a : iter σ₁ I V} {b : iter σ₂ I V}
{s₁ : σ₁} {s₂ : σ₂}

theorem add_iter_sound {i j}
: a.monotonic → b.monotonic → a.terminal_by s₁ i → b.terminal_by s₂ j →
  ⟦(a +' b), (s₁,s₂)⟧ (i+j) = ⟦a, s₁⟧ i + ⟦b, s₂⟧ j :=
λ amono bmono afin bfin, begin
generalize hnij : i+j = n,
induction n with n hn generalizing s₁ s₂ i j,
{ obtain ⟨i0, j0⟩ := sum_zero hnij.symm,
  simp only [semantics', add_zero, i0, j0],
},

obtain (⟨hs,nta,h⟩|⟨hs,ntdi,h⟩|⟨hs,ntb,h⟩) := step_sem_trichotomy a b s₁ s₂,

{ obtain ⟨i', hisucc⟩ := not_terminal_succ nta afin,
  rw hisucc,
  simp only [iter.semantics'],
  simp only [hs,h],
  rw hisucc at *,
  have : i' + j = n,
  { simpa only [nat.succ_add] using hnij },
  rw hn (step_progress afin) bfin this,
  rw add_assoc,
},

{ obtain (⟨ta, tb⟩|⟨nta,ntb⟩) := ntdi,

  { simp [*, semantics_zero, add_iter_monotonic, add_iter_terminal] },

  {
    obtain ⟨i', hisucc⟩ := not_terminal_succ nta afin,
    obtain ⟨j', hjsucc⟩ := not_terminal_succ ntb bfin,
    simp only [hisucc, hjsucc] at *,
    simp only [semantics', hs, h],
    replace afin := step_progress afin,
    have asem_mono := semantics_mono amono afin (nat.le_succ _),
    rw asem_mono,
    have := terminal_by_mono i' i'.succ amono afin (nat.le_succ _),
    have := hn this (step_progress bfin) (nat.succ.inj hnij),
    rw this,
    abel,
  },
},

{ obtain ⟨j', hjsucc⟩ := not_terminal_succ ntb bfin,
  rw hjsucc,
  simp only [iter.semantics'],
  simp only [hs,h],
  rw hjsucc at *,
  have : i + j' = n,
  { simpa only [nat.add_succ] using hnij },
  replace bfin := step_progress bfin,
  rw hn afin bfin this,
  abel,
},
end

end params_binary
end iter
