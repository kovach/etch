import verification.semantics.skip_dense

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
