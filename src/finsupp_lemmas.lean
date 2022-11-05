import data.finsupp.indicator

variables {α β γ : Type*} [add_comm_monoid β]
open_locale classical
noncomputable theory 

namespace finsupp

def sum_range : (α →₀ β) →+ β :=
{ to_fun := λ f, (f.map_domain default) (),
  map_zero' := rfl,
  map_add' := by simp [map_domain_add] }

variables (f g : α →₀ β)
lemma sum_range_eq_sum : f.sum_range = f.sum (λ _ v, v) :=
by simp [sum_range, map_domain] 

@[simp] lemma sum_range_single (x : α) (y : β) : (finsupp.single x y).sum_range = y :=
by simp [sum_range]

@[simp] lemma map_domain_sum_range (h : α → γ) :
  (f.map_domain h).sum_range = f.sum_range :=
by simp [sum_range, ← finsupp.map_domain_comp]

section indicator
/-- Use `s` to construct a `finsupp` with `f` giving the values and `g` giving the indices -/
def indicator' [fintype α] (f : α → β) (g : α → γ) :
  γ →₀ β :=
(indicator finset.univ (λ x _, f x)).map_domain g

lemma indicator'_apply [fintype α] (f : α → β) {g : α → γ}
  (inj : function.injective g) (x : α) : 
  indicator' f g (g x) = f x :=
by simp [indicator', map_domain_apply inj]

open_locale big_operators

@[simp] lemma indicator_sum {s : finset α} (f : α → β) :
  (indicator s (λ x _, f x)).sum_range = ∑ i in s, f i :=
begin
  rw [sum_range_eq_sum, sum],
  simp only [finsupp.indicator_apply, dite_eq_ite, finset.sum_congr],
  rw ← finset.sum_sdiff (finsupp.support_indicator_subset s (λ x _, f x)),
  convert (zero_add _).symm using 2,
  { apply finset.sum_eq_zero, intros x hx, simp at hx, tauto, },
  apply finset.sum_congr rfl,
  intros, simp [*] at *,
end

@[simp] lemma indicator'_sum [fintype α] (f : α → β) (g : α → γ) :
  (indicator' f g).sum_range = ∑ i : α, f i :=
by simp [indicator']


end indicator

end finsupp
