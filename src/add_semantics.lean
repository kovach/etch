-- main theorem: add_iter_sound
import algebra
import base
import add_monotonic
import add_finite

namespace iter

section params_unary
variables {σ I V : Type} [linear_order I]
variables (s t : σ) {a : iter σ I V}

section semantics
variables [add_monoid V]

@[simp] lemma terminal_semantics₁_zero (h : a.terminal t) : a.semantics₁ t = 0 := by simp *

@[simp]
theorem terminal_zero {t} {a : iter σ I V} (m : a.monotonic) (h : a.terminal t) (j:ℕ) : a.semantics' t j = 0 := begin
induction j with _ jh generalizing t,
all_goals {simp *}
end

lemma succ_of_ge_succ : ∀ {i i' : ℕ}, i.succ ≤ i' → ∃ i'':ℕ, i' = i''.succ
| i (nat.succ i'') hle := ⟨_, rfl⟩

theorem semantics_mono {i i'} {s} : a.monotonic → a.terminal_by s i → i ≤ i' → a.semantics' s i = a.semantics' s i' := λ mono fin hle, begin
induction i with i hi generalizing i' s,
{ simp * at * },
obtain ⟨i'', h1⟩ := succ_of_ge_succ hle,
rw h1 at *,
simp only [semantics'],
have : i ≤ i'' := nat.le_of_succ_le_succ hle,
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
  ⟦(a +' b), (s₁,s₂), (i+j)⟧ = ⟦a, s₁, i⟧ + ⟦b, s₂, j⟧ :=
λ amono bmono afin bfin, begin
generalize hnij : i+j = n,
induction n with n hn generalizing s₁ s₂ i j,
{ obtain ⟨i0, j0⟩ := sum_zero.1 hnij.symm,
  simp only [*, semantics', sum_zero, add_zero],
},

obtain (⟨hs,nta,h⟩|⟨hs,ntdi,h⟩|⟨hs,ntb,h⟩) := step_sem_trichotomy a b s₁ s₂,

{ -- a.δ
  obtain ⟨i', hisucc⟩ := not_terminal_succ nta afin,
  rw hisucc at *,
  simp only [semantics'],
  rw [hs,h],
  rw hn (step_progress afin) bfin _,
  { rw add_assoc },
  { simp [*, nat.succ_add] at * },
},

{ -- a.δ, b.δ
  obtain (⟨ta, tb⟩|⟨nta,ntb⟩) := ntdi,

  { simp only [*, terminal_zero, add_zero, add_iter_monotonic, add_iter_terminal] },

  { obtain ⟨i', hisucc⟩ := not_terminal_succ nta afin,
    obtain ⟨j', hjsucc⟩ := not_terminal_succ ntb bfin,
    simp only [hisucc, hjsucc] at *,
    simp only [semantics', hs, h],
    replace afin := step_progress afin,
    rw semantics_mono amono afin (nat.le_succ _),
    have afin' := terminal_by_mono i' i'.succ amono afin (nat.le_succ _),
    have := hn afin' (step_progress bfin) (nat.succ.inj hnij),
    rw this,
    abel,
  },
},

{ -- b.δ
  obtain ⟨j', hjsucc⟩ := not_terminal_succ ntb bfin,
  rw hjsucc at *,
  simp only [iter.semantics'],
  rw [hs, h],
  rw hn afin (step_progress bfin) _,
  { abel },
  { simp [*, nat.add_succ] at * },
},
end

end params_binary
end iter
