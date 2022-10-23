import data.finsupp.indicator

variables {α β : Type*} [add_comm_monoid β]
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

end finsupp
