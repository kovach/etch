import data.finsupp.basic

structure BoundedStream (σ ι α : Type) :=
(next  : σ → σ)
(index : σ → ι)
(value : σ → α)
(ready : σ → bool)
(valid : σ → bool)
(bound : ℕ)

structure status (σ ι α : Type) :=
(next  : σ)
(index : ι)
(value : α)
(ready : bool)
(valid : bool)
(state : σ)

variables {σ ι α : Type}

@[simps]
def BoundedStream.now (s : BoundedStream σ ι α) (x : σ) : status σ ι α :=
{ next  := s.next x,
  index := s.index x,
  value := s.value x,
  ready := s.ready x,
  valid := s.valid x,
  state := x }

noncomputable def BoundedStream.eval₀ [has_zero α] (s : BoundedStream σ ι α) (x : σ) : ι →₀ α :=
if (s.now x).ready = tt then finsupp.single (s.now x).index (s.now x).value else 0

@[simp]
noncomputable def BoundedStream.eval_steps [add_zero_class α] (s : BoundedStream σ ι α) :
  ℕ → σ → option (ι →₀ α)
| 0 x := if (s.now x).valid = ff ∧ (s.now x).ready = ff then some 0 else none
| (n + 1) x := (BoundedStream.eval_steps n (s.next x)).map (λ r, r + s.eval₀ x)

@[simp]
noncomputable def BoundedStream.eval [add_zero_class α] (s : BoundedStream σ ι α) : σ → option (ι →₀ α) :=
s.eval_steps s.bound


