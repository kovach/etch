import Etch.Verification.Semantics.NestedEval

/-!
# Examples

This file instantiates the abstract theorems in `LawfulEval`
in some concrete cases. The examples here correspond to the figures in the paper.

-/

namespace Etch.Verification

variable {ι₁ ι₂ ι₃ : Type} [LinearOrder ι₁] [LinearOrder ι₂] [LinearOrder ι₃] {R : Type}
  [Semiring R]

open Eval (eval)

example (a b c d : ι₁ ⟶ₛ ι₂ ⟶ₛ ι₃ ⟶ₛ R) :
    eval (a * (b + c) * d) = eval a * (eval b + eval c) * eval d := by simp

-- mathport name: «expr∑ᵢ »
local notation "∑ᵢ " s => Stream.contract s

open BigOperators

/-- This is the more Lean appropriate way to state the next example -/
example (a b : ι₁ ⟶ₛ ι₂ ⟶ₛ R) (j : ι₂) :
    (eval (∑ᵢ a * b) : Unit →₀ ι₂ →₀ R) () j = (Finsupp.sumRange (eval a * eval b) : ι₂ →₀ R) j :=
  by simp

-- Unfortunately, Lean doesn't like the notation `eval s x y` because it doesn't know `eval s x` is going to be a function
@[reducible]
noncomputable def eval₂ {ι₁ ι₂ R : Type _} [LinearOrder ι₁] [LinearOrder ι₂] [Semiring R]
    (x : ι₁ ⟶ₛ ι₂ ⟶ₛ R) : ι₁ →₀ ι₂ →₀ R :=
  eval x
#align eval₂ Etch.Verification.eval₂

/-- This is the same as the previous example, but `finsupp.sum_range` 
  is changed to a summation notation that might be more understandable
  because it is closer to "math" notation. -/
example (a b : ι₁ ⟶ₛ ι₂ ⟶ₛ R) (j : ι₂) :
    (eval (∑ᵢ a * b) : Unit →₀ ι₂ →₀ R) () j =
      ∑ i in (eval₂ a * eval₂ b).support, eval₂ a i j * eval₂ b i j :=
  by simp [Finsupp.sumRange_eq_sum, Finsupp.sum, Finsupp.finset_sum_apply]

end Etch.Verification
