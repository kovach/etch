import data.option.basic
import data.fin.tuple.basic


lemma bool.coe_iff_eq_tt (b : bool) : b ↔ b = tt := iff.rfl
@[simp] lemma option.bind_const_none {α β} (x : option α) :
  x.bind (λ _, none) = (none : option β) :=
by cases x; simp
@[simp] lemma option.is_none_ff_iff_is_some {α} (x : option α) :
  x.is_none = ff ↔ x.is_some = tt :=
by cases x; simp

@[simp] lemma fin.tuple_eval_one {n : ℕ} {α : fin (n + 2) → Type*}
  (x₀ : α 0) (x₁ : α 1) (x₂ : Π i : fin n, α i.succ.succ) :
  fin.cons x₀ (fin.cons x₁ x₂) 1 = x₁ := rfl

@[simp] lemma fin.tuple_eval_two {n : ℕ} {α : fin (n + 3) → Type*}
  (x₀ : α 0) (x₁ : α 1) (x₂ : α 2) (x₃ : Π i : fin n, α i.succ.succ.succ) :
  fin.cons x₀ (fin.cons x₁ (fin.cons x₂ x₃)) 2 = x₂ := rfl

universes u v
variables {m : Type u → Type v} [monad m]

/- Technically `m` only needs to be applicative but whatever -/
def fin.tuple_sequence : ∀ {n : ℕ} {α : fin n → Type u},
  (Π i, m (α i)) → m (Π i, α i)
| 0 _ _ := pure default
| (n+1) α x := (x 0) >>= λ r, (fin.tuple_sequence (fin.tail x)) >>= λ x', return (fin.cons r x')

@[simp] lemma fin.tuple_sequence₁ [is_lawful_monad m] {α : fin 1 → Type u} (x : Π i, m (α i)) :
  fin.tuple_sequence x = (x 0) >>= λ r₀, pure (fin.cons r₀ default) :=
by simp [fin.tuple_sequence] with functor_norm

@[simp] lemma fin.tuple_sequence₂ [is_lawful_monad m] {α : fin 2 → Type u} (x : Π i, m (α i)) :
  fin.tuple_sequence x = (x 0) >>= λ r₀, (x 1) >>= λ r₁, pure (fin.cons r₀ $ fin.cons r₁ $ default) :=
by { simp [fin.tuple_sequence] with functor_norm, refl, }

def fin.tuple_some {n : ℕ} {α : fin n → Type u} (x : Π i, option (α i)) : option (Π i, α i) :=
fin.tuple_sequence x
