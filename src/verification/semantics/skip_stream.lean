import verification.semantics.stream_props

-- skip s i : if current index < i, must advance; may advance to first ready index ≥ i.
-- succ s i : if current index ≤ i, must advance; may advance to first ready index > i.

/-
if current index < (i, b), must advance; may advance up to first ready index ≥ (i, b) 
-/

/-- Returns the set of `q` that `s` could skip to if the current state is `x` 
  and it is supposed to skip past `(i, b)` -/
def is_valid_skip {ι α : Type*} [linear_order ι] (s : Stream ι α) (x : s.σ) (i : ι) (b : bool) : set s.σ :=
{q | s.to_order x ≤ (i, b) → (s.to_order x < s.to_order q ∧
  ∀ q' : s.σ, s.to_order x < s.to_order q' → s.to_order q' < s.to_order q → ¬s.ready q')}

structure SkipStream (ι α : Type*) extends Stream ι α :=
(skip : Π x, valid x → ι → bool → σ)

