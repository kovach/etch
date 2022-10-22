import data.finsupp.basic
import control.bifunctor
import finsupp_lemmas

open_locale classical
noncomputable theory

structure Stream (σ ι α : Type) :=
(valid : σ → Prop)
(ready : σ → Prop)
(next  : Π (x : σ), valid x → σ)
(index : Π (x : σ), valid x → ι)
(value : Π (x : σ), ready x → α)

@[ext]
lemma Stream.ext {σ ι α} {s₁ s₂ : Stream σ ι α}
  (h₁ : ∀ x, s₁.valid x ↔ s₂.valid x) (h₂ : ∀ x, s₁.ready x ↔ s₂.ready x) (h₃ : ∀ x H₁ H₂, s₁.next x H₁ = s₂.next x H₂) (h₄ : ∀ x H₁ H₂, s₁.index x H₁ = s₂.index x H₂) (h₅ : ∀ x H₁ H₂, s₁.value x H₁ = s₂.value x H₂) :
  s₁ = s₂ :=
begin
  cases s₁ with v₁ r₁ n₁ i₁ l₁, cases s₂ with v₂ r₂ n₂ i₂ l₂, dsimp only at *,
  obtain rfl : v₁ = v₂ := funext (λ x, propext $ h₁ x), obtain rfl : r₁ = r₂ := funext (λ x, propext $ h₂ x),
  congr; ext, { apply h₃, }, { apply h₄, }, { apply h₅, },
end

@[ext]
structure StreamState (σ ι α : Type) :=
(stream : Stream σ ι α)
(state : σ)

@[ext]
structure StreamExec (σ ι α : Type) extends StreamState σ ι α:=
(bound : ℕ)

notation `↑ₛ`s := StreamExec.to_StreamState s

structure status (σ ι α : Type) :=
(next  : σ)
(index : ι)
(value : α)
(ready : bool)
(valid : bool)
(state : σ)

variables {σ ι α : Type}

@[simps]
instance : bifunctor (Stream σ) :=
{ bimap := λ _ _ _ _ f g s, { s with value := λ x hx, g (s.value x hx), index := λ x hx, f (s.index x hx), } }

instance : is_lawful_bifunctor (Stream σ) :=
{ id_bimap := λ _ _ _, by { ext; simp; exact λ _ _ _, rfl, },
  bimap_bimap := by { intros, ext; simp; exact λ _ _ _, rfl, } }

@[simps]
instance : bifunctor (StreamExec σ) :=
{ bimap := λ _ _ _ _ f g s, { s with stream := bifunctor.bimap f g s.stream } }

instance : is_lawful_bifunctor (StreamExec σ) :=
{ id_bimap := by { intros, ext : 2; simp with functor_norm, },
  bimap_bimap := by { intros, ext : 2; simp with functor_norm, } }

infixr ` <$₁> `:1 := bifunctor.fst
infixr ` <$₂> `:1 := bifunctor.snd

@[simps]
def Stream.now (s : Stream σ ι α) (x : σ) (h₁ : s.valid x) (h₂ : s.ready x) : status σ ι α :=
{ next  := s.next x h₁,
  index := s.index x h₁,
  value := s.value x h₂,
  ready := s.ready x,
  valid := s.valid x,
  state := x }

@[reducible, inline]
def StreamExec.valid (s : StreamExec σ ι α) : Prop := s.stream.valid s.state

@[reducible, inline]
def StreamExec.ready (s : StreamExec σ ι α) : Prop := s.stream.ready s.state

@[simps]
def StreamExec.now (s : StreamExec σ ι α) (h₁ : s.valid) (h₂ : s.ready) : status σ ι α :=
s.stream.now s.state h₁ h₂

@[simps] def StreamExec.δ (s : StreamExec σ ι α) (h : s.valid) : StreamExec σ ι α :=
{ stream := s.stream,
  state := s.stream.next s.state h,
  bound := s.bound.pred }


section
variables {ι' β : Type} (f : ι → ι') (g : α → β)

@[simp] lemma StreamExec.bifunctor_bimap_valid (s : StreamExec σ ι α):
  (bimap f g s).valid ↔ s.valid := iff.rfl
@[simp] lemma StreamExec.bifunctor_bimap_ready (s : StreamExec σ ι α) :
  (bimap f g s).ready ↔ s.ready := iff.rfl

@[simp] lemma StreamExec.bifunctor_bimap_δ (s : StreamExec σ ι α) (h : s.valid) :
  (bimap f g s).δ h = (bimap f g (s.δ h)) := rfl

end

def Stream.eval₀ [has_zero α] (s : Stream σ ι α) (σ₀ : σ) (h₁ : s.valid σ₀) : ι →₀ α :=
if h₂ : s.ready σ₀ then finsupp.single (s.index _ h₁) (s.value _ h₂) else 0

@[simp]
noncomputable def Stream.eval_steps [add_zero_class α] (s : Stream σ ι α) :
  ℕ → σ → ι →₀ α
| 0 _ := 0
| (n + 1) σ₀ := if h₁ : s.valid σ₀ then (Stream.eval_steps n (s.next σ₀ h₁)) + (s.eval₀ _ h₁) else 0

inductive StreamExec.bound_valid_aux : ℕ → StreamExec σ ι α → Prop
| invalid (n : ℕ) {s : StreamExec σ ι α} : ¬s.valid → StreamExec.bound_valid_aux n s
| next_bound_valid {n : ℕ} {s : StreamExec σ ι α} : ∀ (h : s.valid), StreamExec.bound_valid_aux n (s.δ h) → StreamExec.bound_valid_aux (n + 1) s

open StreamExec.bound_valid_aux (invalid next_bound_valid)

def StreamExec.bound_valid (s : StreamExec σ ι α) : Prop := s.bound_valid_aux s.bound

@[simp] lemma StreamExec.bound_valid_zero {s : StreamExec σ ι α} :
  s.bound_valid_aux 0 ↔ ¬s.valid :=
⟨λ h, by { cases h, assumption, }, λ h, invalid _ h⟩

@[simp] lemma StreamExec.bound_valid_succ {s : StreamExec σ ι α} {n : ℕ} :
  s.bound_valid_aux (n + 1) ↔ (∀ (h : s.valid), (s.δ h).bound_valid_aux n) :=
⟨λ h, by { cases h, { intro, contradiction, }, intro, assumption, }, λ h, if H : s.valid then next_bound_valid H (h H) else invalid _ H⟩

def StreamExec.eval [add_zero_class α] (s : StreamExec σ ι α) : ι →₀ α :=
s.stream.eval_steps s.bound s.state

class FinsuppEval (x : Type) (y : out_param Type) :=
(eval : x → y)

instance {β} [add_zero_class β] [FinsuppEval α β] : FinsuppEval (StreamExec σ ι α) (ι →₀ β) :=
⟨λ s, (FinsuppEval.eval <$₂> s).eval⟩

-- These are mainly for testing
instance : FinsuppEval ℕ ℕ := ⟨id⟩
instance : FinsuppEval ℤ ℤ := ⟨id⟩

section defs
variables {ι' β : Type}

@[simp] lemma imap_eval₀_spec [add_comm_monoid α] (f : ι → ι') (s : Stream σ ι α) (σ₀ : σ) (h : s.valid σ₀) :
  (f <$₁> s).eval₀ _ h = (s.eval₀ _ h).map_domain f :=
by { simp only [Stream.eval₀], split_ifs; simp, }

@[simp] lemma imap_eval_steps_spec [add_comm_monoid α] (f : ι → ι') (s : Stream σ ι α) (σ₀ : σ) (n : ℕ) :
  (f <$₁> s).eval_steps n σ₀ = (s.eval_steps n σ₀).map_domain f :=
begin
  induction n with n ih generalizing s σ₀; simp,
  split_ifs; simp [ih, finsupp.map_domain_add], refl,
end

@[simp] lemma bimap_bound_valid_iff (f : ι → ι') (g : α → β) (s : StreamExec σ ι α) :
  (bimap f g s).bound_valid ↔ s.bound_valid :=
by { simp [StreamExec.bound_valid], induction s.bound with n ih generalizing s; simp [*], refl, }

def contract_stream (s : StreamExec σ ι α) : StreamExec σ unit α :=
default <$₁> s

@[simp] lemma contract_stream_spec [add_comm_monoid α] (s : StreamExec σ ι α) :
  (contract_stream s).eval () = finsupp.sum_range s.eval :=
by simp [finsupp.sum_range, contract_stream, StreamExec.eval]

@[simp] lemma contract_stream_bound_valid_iff (s : StreamExec σ ι α) :
  (contract_stream s).bound_valid ↔ s.bound_valid :=
by simp [contract_stream]


end defs

namespace primitives

def externSparseVec_stream : Stream (ℕ × (list ι) × (list α)) ι α :=
{ valid := λ ⟨i, inds, _⟩, i < inds.length,
  ready := λ ⟨i, _, vals⟩, i < vals.length,
  next := λ ⟨i, inds, vals⟩ _, ⟨i + 1, inds, vals⟩,
  index := λ ⟨i , inds, vals⟩ hi, inds.nth_le i hi,
  value := λ ⟨i, inds, vals⟩ hi, vals.nth_le i hi }

def externSparseVec (inds : list ι) (vals : list α) :
  StreamExec (ℕ × (list ι) × (list α)) ι α :=
{ stream := externSparseVec_stream,
  state := ⟨0, inds, vals⟩,
  bound := inds.length }

@[simp] lemma externSparseVec.spec [add_comm_monoid α] (inds : list ι) (vals : list α) :
  (externSparseVec inds vals).eval = (list.map₂ finsupp.single inds vals).sum :=
sorry

def range (n : ℕ) : Stream ℕ ℕ ℕ :=
{ next  := λ k _, k+1,
  index := λ k _, k,
  value := λ k _, k,
  ready := λ _, tt,
  valid := λ k, k < n, }

end primitives
