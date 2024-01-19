import verification.semantics.skip_stream

/-!

# Zero stream

In this file, we define the zero stream, which immediately terminates
producing no output. This stream is important for defining
a nested version of `add`, since `add` requires the value type to 
have a `0`.

## Main results
All the results in this file are trivial (i.e. follow from `false.elim : false → C`)
because the stream itself does not produce anything, and has no valid states.

-/

def Stream.zero (ι : Type) (α : Type*) : Stream ι α :=
{ σ := unit,
  valid := λ _, false,
  ready := λ _, false,
  skip := λ _, false.elim,
  index := λ _, false.elim,
  value := λ _, false.elim } 

variables {ι : Type} [linear_order ι] {α β : Type*}

instance : is_bounded (Stream.zero ι α) :=
⟨⟨empty_relation, empty_wf, λ q, false.drec _⟩⟩

@[simp] lemma Stream.zero_map (f : α → β) :
  (Stream.zero ι α).map f = Stream.zero ι β :=
by { ext; solve_refl, exfalso, assumption, }

variables [add_zero_class α] 

@[simp] lemma Stream.zero_eval :
  (Stream.zero ι α).eval = 0 :=
by { ext q i, rw Stream.eval_invalid, { simp, }, exact not_false, }

instance : is_strict_lawful (Stream.zero ι α) :=
{ mono := λ q, false.drec _,
  skip_spec := λ q, false.drec _,
  strict_mono := ⟨λ q, false.drec _, λ q, false.drec _⟩ }
