import base

section params_binary
variables {σ₁ σ₂ I V : Type} [linear_order I] [decidable_eq σ₁] [decidable_eq σ₂] [add_comm_monoid V]
(a : iter σ₁ I V) (b : iter σ₂ I V)


theorem add_iter_strict    (s₁:σ₁) (s₂:σ₂) : a.strict → b.strict → (a +' b).strict := sorry
end params_binary
