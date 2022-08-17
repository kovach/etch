import data.finsupp.basic

structure Stream (σ ι α : Type) :=
(next  : σ → σ)
(index : σ → ι)
(value : σ → α)
(ready : σ → bool)
(valid : σ → bool)
(bound : ℕ)

structure StreamExec (σ ι α : Type) :=
(stream : Stream σ ι α)
(state : σ)

structure status (σ ι α : Type) :=
(next  : σ)
(index : ι)
(value : α)
(ready : bool)
(valid : bool)
(state : σ)

variables {σ ι α : Type}

@[simps]
def Stream.now (s : Stream σ ι α) (x : σ) : status σ ι α :=
{ next  := s.next x,
  index := s.index x,
  value := s.value x,
  ready := s.ready x,
  valid := s.valid x,
  state := x }

@[simps]
def StreamExec.now (s : StreamExec σ ι α) : status σ ι α :=
s.stream.now s.state

@[simps] def StreamExec.δ (s : StreamExec σ ι α) : StreamExec σ ι α :=
{ stream := s.stream,
  state := s.now.next }

noncomputable def StreamExec.eval₀ [has_zero α] (s : StreamExec σ ι α) : ι →₀ α :=
if s.now.ready = tt then finsupp.single s.now.index s.now.value else 0

@[simp]
noncomputable def StreamExec.eval_steps [add_zero_class α] :
  ℕ → (StreamExec σ ι α) → option (ι →₀ α)
| 0 s := if s.now.valid = ff ∧ s.now.ready = ff then some 0 else none
| (n + 1) s := (StreamExec.eval_steps n s.δ).map (λ r, r + s.eval₀)

@[simp]
noncomputable def StreamExec.eval [add_zero_class α] (s : StreamExec σ ι α) : option (ι →₀ α) :=
s.eval_steps s.stream.bound




