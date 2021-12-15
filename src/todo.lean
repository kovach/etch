import base

section params_binary
variables {σ₁ σ₂ I V : Type} [linear_order I] [decidable_eq σ₁] [decidable_eq σ₂] [add_comm_monoid V]
(a : iter σ₁ I V) (b : iter σ₂ I V)


theorem add_iter_strict    (s₁:σ₁) (s₂:σ₂) : a.strict → b.strict → (a +' b).strict := sorry
-- todo: j needs to be sufficiently large (and statement not true ∀j)
theorem add_iter_sound     (s₁:σ₁) (s₂:σ₂) : ∃ j:ℕ, ⟦(a +' b), (s₁,s₂)⟧ j = ⟦a, s₁⟧ j + ⟦b, s₂⟧ j := sorry

end params_binary
