import verification.semantics.stream_props

-- skip s i : if current index < i, must advance; may advance to first ready index ≥ i.
-- succ s i : if current index ≤ i, must advance; may advance to first ready index > i.

/-
if current index < (i, b), must advance; may advance up to first ready index ≥ (i, b) 
-/

/-- Returns the set of `q` that `s` could skip to if the current state is `x` 
  and it is supposed to skip past `(i, b)` -/
def skip_set {ι α : Type*} [linear_order ι] (s : Stream ι α) (x : s.σ) (i : ι) (b : bool) : set s.σ :=
{q | ∃ (n : ℕ), q = (s.next'^[n] x) ∧ (s.to_order x ≤ (i, b) ↔ 0 < n) ∧
      ∀ m, 0 < m → m < n → s.valid (s.next'^[m] x) → s.ready (s.next'^[m] x) → s.to_order (s.next'^[m] x) ≤ (i, b)}

structure SkipStream (ι α : Type*) [linear_order ι] extends Stream ι α :=
(skip : Π x, valid x → ι → bool → σ)
(hskip : ∀ x hx i b, skip x hx i b ∈ skip_set _ x i b)



