import Etch.Verification.Semantics.SkipStream

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

namespace Etch.Verification

def Stream.zero (ι : Type) (α : Type _) : Stream ι α
    where
  σ := Unit
  valid _ := False
  Ready _ := False
  skip _ := False.elim
  index _ := False.elim
  value _ := False.elim
#align Stream.zero Etch.Verification.Stream.zero

variable {ι : Type} [LinearOrder ι] {α β : Type _}

instance : IsBounded (Stream.zero ι α) :=
  ⟨⟨EmptyRelation, empty_wf, fun q => False.drec _⟩⟩

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `solve_refl #[] -/
@[simp]
theorem Stream.zero_map (f : α → β) : (Stream.zero ι α).map f = Stream.zero ι β :=
  by
  ext <;>
    trace
      "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `solve_refl #[]"
  exfalso
  assumption
#align Stream.zero_map Etch.Verification.Stream.zero_map

variable [AddZeroClass α]

@[simp]
theorem Stream.zero_eval : (Stream.zero ι α).eval = 0 :=
  by
  ext (q i)
  rw [Stream.eval_invalid]
  · simp
  exact not_false
#align Stream.zero_eval Etch.Verification.Stream.zero_eval

instance : IsStrictLawful (Stream.zero ι α)
    where
  mono q := False.drec _
  skip_spec q := False.drec _
  StrictMono := ⟨fun q => False.drec _, fun q => False.drec _⟩

end Etch.Verification
