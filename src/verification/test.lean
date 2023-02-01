import verification.stream_add
import verification.stream_multiply
import verification.stream_replicate
import verification.stream_props

local infixr ` ↠ `:50 := SimpleStream

section
variables {ι₁ ι₂ ι₃ : Type} [linear_order ι₁] [linear_order ι₂]
  [linear_order ι₃] {R : Type} [semiring R]

open Eval (eval)

local notation `∑ᵢ ` s := s.contract

local notation (name := bool_add) a ` && ` b := a + b

-- 
noncomputable instance SimpleStream.AddZeroEval_weird :
  AddZeroEval (ι₁ ↠ ι₂ ↠ ι₃ ↠ R) ι₁ (ι₂ →₀ ι₃ →₀ R) :=
  SimpleStream.AddZeroEval

example (a b c d : ι₁ ↠ ι₂ ↠ ι₃ ↠ R)  : 
  eval (a * (b + c) * d) =
  (eval a) * ((eval b) + (eval c)) * (eval d) :=
by simp

example [semiring R] (a b c : SimpleStream ι₁ (SimpleStream ι₂ R)) :
  eval ((a + b) * c) = eval a * eval c + eval b * eval c :=
by simp [add_mul]

end

open_locale big_operators

section
variables {ι₁ ι₂ ι₃ : Type} [linear_order ι₁] [linear_order ι₂]
  [linear_order ι₃] {R : Type} [semiring R]

local notation `∑ᵢ ` s := s.contract

-- Unfortunately, Lean doesn't like the notation `eval s x y` because it doesn't know `eval s x` is going to be a function
-- TODO: Fix
@[reducible] def eval {ι₁ ι₂ α₁ R : Type*} [has_zero R] [Eval α₁ ι₁ (ι₂ →₀ R)]
  (x : α₁) : ι₁ →₀ ι₂ →₀ R := Eval.eval x

@[reducible] def eval3 {ι₁ ι₂ ι₃ α₁ R : Type*} [has_zero R] [Eval α₁ ι₁ (ι₂ →₀ ι₃ →₀ R)]
  (x : α₁) : ι₁ →₀ ι₂ →₀ ι₃ →₀ R := Eval.eval x

local attribute [simp] eval finsupp.sum_range_eq_sum finsupp.sum
  finsupp.finset_sum_apply

example (a b : ι₁ ↠ ι₂ ↠ R)
  (j : ι₂) : eval (∑ᵢ (a * b)) () j =
    ∑ i in (eval a * eval b).support,
    (eval a i j * eval b i j) :=
by rw Eval.contract'; simp

end

constants (n₁ n₂ n₃ : ℕ)

variables {R : Type} [semiring R]

variables {ι₁ ι₂ ι₃ : Type} [linear_order ι₁] [linear_order ι₂] [linear_order ι₃]
          (m₁ : fin n₁ ≃o ι₁)
          (m₂ : fin n₂ ≃o ι₂)
          (m₃ : fin n₃ ≃o ι₃)

local notation `⇑₁` := SimpleStream.replicate' (m₁ : fin n₁ ↪o ι₁)
local notation `⇑₂` := SimpleStream.replicate' (m₂ : fin n₂ ↪o ι₂)
local notation `⇑₃` := SimpleStream.replicate' (m₃ : fin n₃ ↪o ι₃)

section

local notation `∑ᵢ ` s := s.contract

local attribute [simp] eval finsupp.sum_range_eq_sum finsupp.sum
  finsupp.finset_sum_apply finsupp.const
  SimpleStream.replicate'.spec_equiv -- TODO: tag this as @[simp]?

example (c : R) (k : ι₃) : Eval.eval (⇑₃ c) k = c :=
by simp [Eval.eval]

example (v w : ι₃ ↠ R) (k : ι₃) : Eval.eval (v * w) k = (Eval.eval v k) * (Eval.eval w k) :=
by simp

example (c : R) (v : ι₃ ↠ R) (k : ι₃) : Eval.eval ((⇑₃ c) * v) k = c * (Eval.eval v k) :=
by { simp_rw [MulEval.hmul, Eval.eval], simp }

-- Help instance inferrer out a bit.
noncomputable instance test_instance :
Eval (StreamExec unit R) unit R := infer_instance
noncomputable instance test_instance2 {ι} [linear_order ι] :
Eval (StreamExec unit (ι ↠ R)) unit (ι →₀ R) := infer_instance

noncomputable def matmul (a : ι₁ ↠ ι₂ ↠ R) (b : ι₂ ↠ ι₃ ↠ R) :=
(λ (r : ι₂ ↠ R), ∑ᵢ ((⇑₃ <§₂> r) * b)) <§₂> a

example (a : ι₁ ↠ ι₂ ↠ R) (b : ι₂ ↠ ι₃ ↠ R) (i : ι₁) (k : ι₃) :
  eval3 (matmul m₃ a b) i () k =
    ∑ j in (eval a i).support ∪ (eval b).support,
    (eval a i j * eval b j k) :=
begin
  simp_rw [eval, eval3],
  sorry -- TODO: one day, hopefully soon
end

end
