import verification.semantics.nested_eval

/-!
# Examples

This file instantiates the abstract theorems in `LawfulEval`
in some concrete cases. The examples here correspond to the figures in the paper.

-/

variables {ι₁ ι₂ ι₃ : Type} [linear_order ι₁] [linear_order ι₂]
  [linear_order ι₃] {R : Type} [semiring R]

open Eval (eval)

example (a b c d : ι₁ ⟶ₛ ι₂ ⟶ₛ ι₃ ⟶ₛ R)  : 
  eval (a * (b + c) * d) =
  (eval a) * ((eval b) + (eval c)) * (eval d) :=
by simp

local notation `∑ᵢ ` s := s.contract

open_locale big_operators

/-- This is the more Lean appropriate way to state the next example -/
example (a b : ι₁ ⟶ₛ ι₂ ⟶ₛ R) (j : ι₂) :
  (eval (∑ᵢ (a * b)) : unit →₀ ι₂ →₀ R) () j =
  (finsupp.sum_range (eval a * eval b) : ι₂ →₀ R) j :=
by simp

-- Unfortunately, Lean doesn't like the notation `eval s x y` because it doesn't know `eval s x` is going to be a function
@[reducible] noncomputable def eval₂ {ι₁ ι₂ R : Type*} [linear_order ι₁] [linear_order ι₂] [semiring R]
  (x : ι₁ ⟶ₛ ι₂ ⟶ₛ R) : ι₁ →₀ ι₂ →₀ R := eval x

/-- This is the same as the previous example, but `finsupp.sum_range` 
  is changed to a summation notation that might be more understandable
  because it is closer to "math" notation. -/
example (a b : ι₁ ⟶ₛ ι₂ ⟶ₛ R) (j : ι₂) :
  (eval (∑ᵢ (a * b)) : unit →₀ ι₂ →₀ R) () j =
  ∑ i in (eval₂ a * eval₂ b).support,
    (eval₂ a i j * eval₂ b i j) :=
by simp [finsupp.sum_range_eq_sum, finsupp.sum, finsupp.finset_sum_apply]
