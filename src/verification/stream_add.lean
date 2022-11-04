import verification.stream_props
import verification.misc

open_locale classical
noncomputable theory

variables {σ σ₁ σ₂ ι α : Type}
  [linear_order ι]
  [non_unital_semiring α]

@[simps]
def Stream.add (a : Stream σ₁ ι α) (b : Stream σ₂ ι α) : Stream (σ₁ × σ₂) ι α :=
{ valid := λ s, a.valid s.1 ∨ b.valid s.2,
  ready := λ s, a.ready s.1 ∨ b.ready s.2,
  next := λ s h, (if H : a.to_order s.1 ≤ b.to_order s.2 then a.next s.1 (valid_of_le_or h H) else s.1, 
                  if H : b.to_order s.2 ≤ a.to_order s.1 then b.next s.2 (valid_of_le_or h.symm H) else s.2),
  index := λ s h, option.get (show (min (a.index' s.1) (b.index' s.2)).is_some, by simpa),
  value := λ s h, (if h₁ : a.ready s.1 then a.value _ h₁ else 0) +
                  (if h₂ : b.ready s.2 then b.value _ h₂ else 0) }

def StreamExec.add (a : StreamExec σ₁ ι α) (b : StreamExec σ₂ ι α) : StreamExec (σ₁ × σ₂) ι α :=
{ stream := a.stream.add b.stream,
  state := (a.state, b.state),
  bound := a.bound + b.bound }

/-
lemma : ∀ n, ∃ (k₁ k₂), s.t. n ≤ k₁ + k₂ ∧ (a + b).eval_steps n = (a.eval_steps k₁ + b.eval_steps k₂)

WLOG k₁, k₂ ≤ bound
-/

