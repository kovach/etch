import verification.semantics.dense

/-!
# Stream replicate

This file defines replicate, which is a specialization of the dense vector 
stream to a constant function.

**Note: the current version of the paper uses the terminology *expand*, which was from a previous version of the paper.
The terms *replicate* and *expand* should be considered to be synonymous**.

-/

variables {α β : Type*}

@[derive is_bounded]
def Stream.replicate (n : ℕ) (v : α) : Stream (fin n) α :=
Stream.denseVec (λ _, v)

@[simp] lemma Stream.replicate_map (f : α → β) (n : ℕ) (v : α) :
  (Stream.replicate n v).map f = Stream.replicate n (f v) := rfl

variables [add_zero_class α]

instance (n : ℕ) (v : α) : is_strict_lawful (Stream.replicate n v) :=
by { dunfold Stream.replicate, apply_instance, }

@[simp] lemma Stream.replicate_eval (n : ℕ) (v : α) (j : fin n) :
  (Stream.replicate n v).eval (0 : fin (n + 1)) j = v :=
by { dunfold Stream.replicate, simp, }
