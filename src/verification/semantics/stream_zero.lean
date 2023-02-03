import verification.semantics.stream
import verification.semantics.stream_props

variables {ι : Type} {α β : Type*}

@[simps]
instance [has_zero β] : has_zero (Stream ι β) :=
⟨{ σ := unit,
  valid := λ _, false,
  ready := λ _, false,
  next := λ _, false.elim,
  index := λ _, false.elim,
  value := λ _, false.elim }⟩

@[simp] lemma Stream.zero_eval [add_zero_class β] (n : ℕ) (x : unit) :
  (0 : Stream ι β).eval_steps n x = 0 := Stream.eval_invalid not_false _

@[simps]
instance [has_zero β] : has_zero (StreamExec ι β) := ⟨
{ stream := 0,
  state := (),
  bound := 0,
  bound_valid := Stream.bound_valid.start _ not_false }⟩

@[simp] lemma StreamExec.zero_eval [add_zero_class β] :
  (0 : StreamExec ι β).eval = 0 := rfl

instance [has_zero β] [linear_order ι] : has_zero (SimpleStream ι β) :=
⟨{ simple :=
{ monotonic := λ x h, h.elim,
  reduced := λ x h, h.elim }, ..(0 : StreamExec ι β) }⟩

@[simp] lemma SimpleStream.zero_eval [add_zero_class β] [linear_order ι] :
  StreamExec.eval ((0 : SimpleStream ι β) : StreamExec ι β) = 0 := rfl
