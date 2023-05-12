import Etch.Verification.Semantics.Dense

/-!
# Stream replicate

This file defines replicate, which is a specialization of the dense vector 
stream to a constant function.

**Note: the current version of the paper uses the terminology *expand*, which was from a previous version of the paper.
The terms *replicate* and *expand* should be considered to be synonymous**.

-/

namespace Etch.Verification

variable {α β : Type _}

def Stream.replicate (n : ℕ) (v : α) : Stream (Fin n) α :=
  Stream.denseVec fun _ => v deriving IsBounded
#align Stream.replicate Etch.Verification.Stream.replicate

@[simp]
theorem Stream.replicate_map (f : α → β) (n : ℕ) (v : α) :
    (Stream.replicate n v).map f = Stream.replicate n (f v) :=
  rfl
#align Stream.replicate_map Etch.Verification.Stream.replicate_map

variable [AddZeroClass α]

instance (n : ℕ) (v : α) : IsStrictLawful (Stream.replicate n v) :=
  by
  dsimp only [Stream.replicate]
  infer_instance

@[simp]
theorem Stream.replicate_eval (n : ℕ) (v : α) (j : Fin n) :
    (Stream.replicate n v).eval (0 : Fin (n + 1)) j = v :=
  by
  dsimp only [Stream.replicate]
  simp
#align Stream.replicate_eval Etch.Verification.Stream.replicate_eval

end Etch.Verification
