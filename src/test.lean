#check heq

variables {α : Sort*}


--λ {a a' : α} (h : a == a'), heq.rec (λ (h₂ : α = α), eq.refl a) h (eq.refl α)

universes u

lemma eq_of_heq' {α : Sort u} {a a' : α} (h : a == a') : a = a' :=
have ∀ (α' : Sort u) (a' : α') (h₁ : @heq α a α' a') (h₂ : α = α'), (eq.rec_on h₂ a : α') = a', from
  λ (α' : Sort u) (a' : α') (h₁ : @heq α a α' a'), heq.rec_on h₁ (λ h₂ : α = α, rfl),
show (eq.rec_on (eq.refl α) a : α) = a', from
  this α a' h (eq.refl α)

#reduce (@eq_of_heq' α)


-- lemma eq_of_heq'' {a a' : α} (h : a == a') : a = a' :=
-- (heq.rec (λ (h₂ : α = α), eq.refl a) h (eq.refl α) : a = a')

-- #reduce eq_of_heq