import verification.stream_add
import verification.stream_multiply

local infixr ` ↠ `:50 := SimpleStream

section
variables {ι₁ ι₂ ι₃ : Type} [linear_order ι₁] [linear_order ι₂]
  [linear_order ι₃] {R : Type} [semiring R] 

open Eval (eval)

local notation ` ∑ᵢ ` s := s.contract

example (a b c d : ι₁ ↠ ι₂ ↠ R)  : 
  eval (a * b + c + d) =
  (eval a) * (eval b) + (eval c) + (eval d) :=
by simp

example [semiring R] (a b c : SimpleStream ι₁ (SimpleStream ι₂ R)) :
  eval ((a + b) * c) = eval a * eval c + eval b * eval c :=
by simp [add_mul]

end

open_locale big_operators

section
variables {ι₁ ι₂ ι₃ : Type} [linear_order ι₁] [linear_order ι₂]
  [linear_order ι₃] {R : Type} [semiring R]

local notation ` ∑ᵢ ` s := SimpleStream.contract s

-- Unfortunately, Lean doesn't like the notation `eval s x y` because it doesn't know `eval s x` is going to be a function
-- TODO: Fix
@[reducible] def eval {ι₁ ι₂ α₁ R : Type*} [has_zero R] [Eval α₁ ι₁ (ι₂ →₀ R)]
  (x : α₁) : ι₁ →₀ ι₂ →₀ R := Eval.eval x

local attribute [simp] eval finsupp.sum_range_eq_sum finsupp.sum
  finsupp.finset_sum_apply

example (a b : ι₁ ↠ ι₂ ↠ R)
  (j : ι₂) : eval (∑ᵢ (a * b)) () j =
    ∑ i in (eval a * eval b).support,
    (eval a i j * eval b i j) :=
by rw Eval.contract'; simp

end
