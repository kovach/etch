import Etch.Verification.Semantics.Dense

/-!
# Stream replicate

This file defines replicate, which is a specialization of the dense vector 
stream to a constant function.

**Note: the current version of the paper uses the terminology *expand*, which was from a previous version of the paper.
The terms *replicate* and *expand* should be considered to be synonymous**.

-/

namespace Etch.Verification

variable {α β : Type _} (n : ℕ) (v : α)

set_option linter.uppercaseLean3 false

def Stream.replicate : Stream (Fin n) α :=
  Stream.denseVec fun _ => v
#align Stream.replicate Etch.Verification.Stream.replicate

attribute [reducible] Stream.replicate in
section

@[simp]
theorem Stream.replicate_map (f : α → β) :
    (Stream.replicate n v).map f = Stream.replicate n (f v) := rfl
#align Stream.replicate_map Etch.Verification.Stream.replicate_map

instance : IsBounded (Stream.replicate n v) := inferInstance

variable [AddZeroClass α]
instance : IsStrictLawful (Stream.replicate n v) := inferInstance

@[simp]
theorem Stream.replicate_eval (j : Fin n) :
    (Stream.replicate n v).eval 0 j = v := by simp
#align Stream.replicate_eval Etch.Verification.Stream.replicate_eval

end

end Etch.Verification
