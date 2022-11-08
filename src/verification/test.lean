import verification.stream_add
import verification.stream_multiply

variables {ι₁ ι₂ ι₃ : Type} [linear_order ι₁] [linear_order ι₂]
  [linear_order ι₃]

open Eval (eval)

example (a b c : SimpleStream ι₁ (SimpleStream ι₂ ℤ))  : 
  eval (a * b + c) = (eval a) * (eval b) + eval c := by simp
