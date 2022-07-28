import data.finsupp.indicator

variables {α β : Type*} [add_comm_monoid β]
noncomputable theory 

namespace finsupp

def sum_range (f : α →₀ β) : β :=
(f.map_domain default) ()

variables (f g : α →₀ β)
lemma sum_range_eq_sum : f.sum_range = f.sum (λ _ v, v) :=
by simp [sum_range, map_domain] 

@[simp] lemma sum_range_add : (f + g).sum_range = f.sum_range + g.sum_range :=
by simp [sum_range, map_domain_add]

@[simp] lemma sum_range_zero : (0 : α →₀ β).sum_range = 0 :=
by simp [sum_range]

@[simp] lemma sum_range_single (x : α) (y : β) : (finsupp.single x y).sum_range = y :=
by simp [sum_range]

/- This shows sum_range is a monoid homomorphism. We could explicitly write an `add_monoid_hom` def -/


end finsupp
