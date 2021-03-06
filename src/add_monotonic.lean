-- main theorem: add_iter_monotonic
import algebra
import algebra.group
import algebra.group.defs
import tactic
import logic.relation

import combinators

namespace iter

section params_unary
variables {σ I V : Type} [linear_order I]
{a : iter σ I V}
variables (s t : σ)

lemma mono_iff_delta_mono  : a.monotonic ↔ ∀ s, a.ι s ≤ a.ι (a.δ s) := begin
split,
{ intros m t,
  exact m _ _ (transition.step a)},
{ intros hstep s t path,
  obtain ⟨len, h⟩ := index_of_path path,
  rw h at *,
  clear h t path,
  induction len with _ h generalizing s,
    { exact le_refl _ },
    { rw step_succ,
      exact (hstep s).trans (h (a.δ s)) }
},
end

end params_unary

section params_binary
variables {σ₁ σ₂ I V : Type} [linear_order I] [add_monoid V]
{a : iter σ₁ I V} {b : iter σ₂ I V}

lemma add_ι_min {s} : (a+'b).ι s = min (a.ι s.1) (b.ι s.2) := begin
cases s with s₁ s₂,
simp only [ι, add_iter, add_emit, min_def],
split_ifs with h1 h2 h3,
repeat {refl}, -- 2
repeat {simp only [gt_iff_lt, not_lt] at *},
{ exfalso, exact h2 (le_of_lt h1) },
{ exfalso, exact not_lt_of_le h h3 },
{ -- main case
  replace h := h.antisymm h1,
  cases h4 : a.emit s₁ with v1; cases h5 : b.emit s₂ with v2,
  repeat { try {cases v1}, try {cases v2}, simpa only [iter.ι, h4, h5] using h },
},
{ exfalso, exact h h3 },
end

lemma step_dichotomy_left (s₁:σ₁)(s₂:σ₂) : ((a +'b).δ (s₁,s₂)).1 = a.δ s₁ ∨ ((a +'b).δ (s₁,s₂)).1 = s₁ := begin
simp only [add_iter, iter.δ], split_ifs, tidy,
end
lemma step_dichotomy_right (s₁:σ₁)(s₂:σ₂) : ((a +'b).δ (s₁,s₂)).2 = b.δ s₂ ∨ ((a +'b).δ (s₁,s₂)).2 = s₂ := begin
simp only [add_iter, iter.δ], split_ifs, tidy,
end

theorem add_iter_monotonic : a.monotonic → b.monotonic → (a +' b).monotonic := begin
intros m1 m2, simp only [mono_iff_delta_mono],

rintro ⟨t₁, t₂⟩, simp only [add_ι_min],
apply min_le_min _ _,

{ obtain (h|h) := step_dichotomy_left t₁ t₂; rw h,
  apply mono_iff_delta_mono.1 m1,
  exact le_refl _ },

{ obtain (h|h) := step_dichotomy_right t₁ t₂; rw h,
  apply mono_iff_delta_mono.1 m2,
  exact le_refl _ }
end

end params_binary

end iter
