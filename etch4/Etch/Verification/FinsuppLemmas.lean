import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Indicator

variable {α β γ : Type _} [AddCommMonoid β]

open Classical

noncomputable section

namespace Finsupp

def sumRange : (α →₀ β) →+ β where
  toFun f := (f.mapDomain default) ()
  map_zero' := rfl
  map_add' := by simp [mapDomain_add]
#align finsupp.sum_range Finsupp.sumRange

variable (f g : α →₀ β)

theorem sumRange_eq_sum : sumRange f = f.sum fun _ v => v := by simp [sumRange, mapDomain]
#align finsupp.sum_range_eq_sum Finsupp.sumRange_eq_sum

@[simp]
theorem sumRange_single (x : α) (y : β) : sumRange (single x y) = y := by simp [sumRange]
#align finsupp.sum_range_single Finsupp.sumRange_single

@[simp]
theorem mapDomain_sumRange (h : α → γ) : sumRange (f.mapDomain h) = sumRange f := by
  simp [sumRange, ← mapDomain_comp]
#align finsupp.map_domain_sum_range Finsupp.mapDomain_sumRange

end Finsupp
